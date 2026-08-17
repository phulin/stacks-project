import Formalization.Books.Categories.Unit37.PresheavesOfGroupoids
import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Categories, Chapter 38: Categories fibred in sets

The source's discrete fibres are Mathlib's `IsDiscrete` categories.  The
category associated to a set-valued presheaf is the existing
CoGrothendieck construction from Units 36 and 37, specialized to the
canonical discrete category on each value of the presheaf.
-/

namespace Formalization.Books.Categories.Unit38

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.ObjectProperty
open Opposite
open Formalization.Books.Categories.Unit03
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36
open Formalization.Books.Categories.Unit37

universe vC uC vS uS v u

noncomputable section

/-! ## Discrete fibres -/

/- Mathlib's `IsDiscrete` is exactly the source definition: a morphism forces
   its endpoints to be equal, and every hom type is subsingleton.  We use it
   directly below instead of introducing a parallel predicate. -/

/-- A functor is a category fibred in sets when it is fibred in groupoids and
all its fibre categories are discrete. -/
def IsCategoryFibredInSets
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧
    ∀ U : C, IsDiscrete (Functor.Fiber p U)

theorem isCategoryFibredInSets_iff_isFibered_and_discreteFibres
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    IsCategoryFibredInSets p ↔
      p.IsFibered ∧ ∀ U : C, IsDiscrete (Functor.Fiber p U) := by
  sorry

/-! ## The fixed-base 2-category -/

/-- The object property selecting discrete fibres in the fixed-base
fibred-category interface from Unit 33. -/
def IsDiscreteFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsDiscrete (Functor.Fiber (structureFunctor X.underlying) U)

def discreteFibredCategoryObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  IsDiscreteFibredCategoryOver

/-- The source's 2-category of categories fibred in sets over a fixed base. -/
abbrev CategoriesFibredInSetsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C)
    (discreteFibredCategoryObjectProperty (C := C))

/- A functor over the base automatically preserves strongly cartesian arrows
when its target has discrete fibres: all arrows in a category fibred in
groupoids are strongly cartesian. -/
theorem mapsStronglyCartesian_to_discreteFibred
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    MapsStronglyCartesian
      (structureFunctor X.underlying) (structureFunctor Y.underlying)
      (overFunctor F) := by
  sorry

/-- The source-facing constructor for a 1-morphism over the base; the
preservation field is automatic for a discrete-fibred target. -/
def fibredCategoryOverHomOfDiscrete
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    FibredCategoryOverHom X Y where
  underlying := F
  preserves := mapsStronglyCartesian_to_discreteFibred hY F

/-- The 2-morphisms in the fixed-base 2-category are identities, expressed as
local discreteness of all its hom-categories. -/
theorem categoriesFibredInSetsOver_is_locallyDiscrete
    (C : Cat.{v, u}) :
    Bicategory.IsLocallyDiscrete (CategoriesFibredInSetsOver C) := by
  sorry

theorem categoriesFibredInSetsOver_is_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory (CategoriesFibredInSetsOver C) := by
  sorry

/-! ## 2-fibre products -/

/-- The Unit 35 two-fibre product package with the additional assertion that
all fibres of its apex are discrete. -/
structure FibredInSetsTwoFibreProduct
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  product : FibredTwoFibreProduct.{u, v, v, u} F G
  fibres_are_discrete : ∀ U : C,
    IsDiscrete (Functor.Fiber product.diagram.base U)

theorem categoriesFibredInSets_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsDiscreteFibredCategoryOver X)
    (hY : IsDiscreteFibredCategoryOver Y)
    (hS : IsDiscreteFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInSetsTwoFibreProduct F G) := by
  sorry

/-! ## The presheaf construction -/

/-- Turn a set-valued presheaf into a presheaf of discrete categories. -/
def setPresheafToCat
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    Cᵒᵖ ⥤ Cat.{uS, uS} where
  obj U := Cat.of (Discrete (F.obj U))
  map {U V} f :=
    (Discrete.functor (fun x => Discrete.mk (F.map f x))).toCatHom
  map_id := fun U => by
    apply Cat.Hom.ext
    apply Discrete.functor_ext
    intro Z
    have hZ : F.map (𝟙 U) Z = Z :=
      congrArg (fun h : F.obj U ⟶ F.obj U => h Z) (F.map_id U)
    exact congrArg Discrete.mk hZ
  map_comp := fun {U V W} f g => by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro Z
      have hZ : F.map (f ≫ g) Z.as = F.map g (F.map f Z.as) :=
        congrArg (fun h : F.obj U ⟶ F.obj W => h Z.as) (F.map_comp f g)
      change Discrete.mk (F.map (f ≫ g) Z.as) =
        Discrete.mk (F.map g (F.map f Z.as))
      exact congrArg Discrete.mk hZ
    · intro Z Z' q
      rcases Z with ⟨Z⟩
      rcases Z' with ⟨Z'⟩
      rcases q with ⟨⟨h⟩⟩
      change Z = Z' at h
      subst Z'
      rfl

/-- The category `\mathcal S_F` associated to a set-valued presheaf. -/
abbrev setPresheafCategory
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :=
  groupoidPresheafCategory (setPresheafToCat F)

/-- The projection `p_F : \mathcal S_F ⥤ C`. -/
abbrev setPresheafProjection
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    setPresheafCategory F ⥤ C :=
  groupoidPresheafProjection (setPresheafToCat F)

/-- The restriction functor corresponding to a base arrow. -/
abbrev setPresheafRestriction
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) {V U : C} (f : V ⟶ U) :=
  groupoidPresheafRestriction (setPresheafToCat F) f

theorem setPresheafRestriction_comp
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    setPresheafRestriction F (g ≫ f) =
      setPresheafRestriction F f ⋙ setPresheafRestriction F g := by
  exact groupoidPresheafRestriction_comp (setPresheafToCat F) g f

@[simp]
theorem setPresheafProjection_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    (setPresheafProjection F).obj X = X.base :=
  rfl

@[simp]
theorem setPresheafProjection_map
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    (setPresheafProjection F).map f = f.base :=
  rfl

/-- The CoGrothendieck category has the source's displayed object and
morphism data: its objects have a base object and a value in the fibre, while
its morphisms have a base arrow and a fibre arrow. -/
theorem setPresheaf_category_isFibredInSets
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    IsCategoryFibredInSets (setPresheafProjection F) := by
  sorry

/-! ## The presheaf correspondence -/

/-- A discrete-valued presheaf of categories is the split model of a
category fibred in sets. -/
def discretePresheafObjectProperty
    {C : Type uC} [Category.{vC} C] :
    ObjectProperty (Cᵒᵖ ⥤ Cat.{vC, vC}) :=
  fun F => ∀ U : C, IsDiscrete (F.obj (Opposite.op U))

abbrev SplitPresheavesInSets
    (C : Type uC) [Category.{vC} C] :=
  (discretePresheafObjectProperty (C := C)).FullSubcategory

/-- The object part of the presheaf-to-split-fibred-category correspondence. -/
def setPresheafAsDiscretePresheaf
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type vC) : SplitPresheavesInSets C where
  obj := setPresheafToCat F
  property := by
    intro U
    change IsDiscrete (Discrete (F.obj (Opposite.op U)))
    infer_instance

theorem categoriesFibredInSets_are_presheaves
    {C : Type uC} [Category.{vC} C] :
    Nonempty
      ((Cᵒᵖ ⥤ Type vC) ≌
        SplitPresheavesInSets C) := by
  sorry

theorem categoriesFibredInSetsOver_equivalent_to_presheaves
    {C : Type uC} [Category.{vC} C] :
    Nonempty
      ((Cᵒᵖ ⥤ Type vC) ≌
        CategoriesFibredInSetsOver (Cat.of C)) := by
  sorry

/-- Every category fibred in sets is equivalent over its base to the
CoGrothendieck category of a set-valued presheaf.  This is the usable
objectwise form of the source's equivalence of categories. -/
theorem fibredInSets_equivalent_to_presheaf_construction
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      IsFibredEquivalenceOver p (setPresheafProjection F) := by
  sorry

/-- The object-valued presheaf attached to a fibred category in sets exists;
its value at `U` is the object type of the fibre over `U`. -/
theorem fibredInSets_object_presheaf_exists
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    ∃ F : Cᵒᵖ ⥤ Type uS,
      ∀ U : C, Nonempty (F.obj (Opposite.op U) ≃ Functor.Fiber p U) := by
  sorry

noncomputable def fibredInSetsObjectPresheaf
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) :
    Cᵒᵖ ⥤ Type uS :=
  Classical.choose (fibredInSets_object_presheaf_exists p hp)

theorem fibredInSetsObjectPresheaf_obj_equiv
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) (hp : IsCategoryFibredInSets p) (U : C) :
    Nonempty
      ((fibredInSetsObjectPresheaf p hp).obj (Opposite.op U) ≃
        Functor.Fiber p U) := by
  exact (Classical.choose_spec (fibredInSets_object_presheaf_exists p hp)) U

/-! ## The representable example -/

@[simp]
theorem sliceProjection_object_of_hom
    {C : Type uC} [Category.{vC} C] (X U : C) (h : U ⟶ X) :
    (Over.forget X).obj (Over.mk h) = U :=
  rfl

theorem sliceProjection_fibre_is_discrete
    {C : Type uC} [Category.{vC} C] (X U : C) :
    IsDiscrete (Functor.Fiber (Over.forget X) U) := by
  sorry

theorem sliceProjection_isFibredInSets
    {C : Type uC} [Category.{vC} C] (X : C) :
    IsCategoryFibredInSets (Over.forget X) := by
  sorry

/-- The representable presheaf corresponds to the slice category `C/X`. -/
theorem representable_presheaf_slice_equivalence
    {C : Type uC} [Category.{vC} C] (X : C) :
    IsFibredEquivalenceOver (Over.forget X)
      (setPresheafProjection (representablePresheaf X)) := by
  sorry

end

end Formalization.Books.Categories.Unit38
