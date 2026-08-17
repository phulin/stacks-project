import Formalization.Books.Categories.Unit03.Opposite
import Formalization.Books.Categories.Unit37.PresheavesOfGroupoids
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Discrete

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

universe vC uC vS uS u₁ v₁ v u

noncomputable section

/-! ## Discrete fibres -/

/- Mathlib's `IsDiscrete` is exactly the source definition: a morphism forces
   its endpoints to be equal, and every hom type is subsingleton.  We use it
   directly below instead of introducing a parallel predicate. -/

theorem isDiscrete_iff_every_morphism_is_eqToHom
    {C : Type*} [Category* C] :
    IsDiscrete C ↔
      ∀ {X Y : C} (f : X ⟶ Y), ∃ h : X = Y, f = eqToHom h := by
  constructor
  · intro h X Y f
    exact ⟨h.eq_of_hom f, @Subsingleton.elim _ (h.subsingleton X Y) _ _⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro X Y
      constructor
      intro f g
      rcases h f with ⟨hf, hff⟩
      rcases h g with ⟨hg, hgg⟩
      rw [hff, hgg]
    · intro X Y f
      exact (h f).choose

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
  constructor
  · rintro ⟨hp, hdiscrete⟩
    have h := (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp
    exact ⟨h.2, hdiscrete⟩
  · rintro ⟨hfibred, hdiscrete⟩
    refine ⟨(fibredInGroupoids_iff_fibred_groupoid_fibres p).mpr ?_, hdiscrete⟩
    exact ⟨fun U => by
      refine ⟨fun {X Y} f => ?_⟩
      have hf : f = eqToHom ((hdiscrete U).eq_of_hom f) :=
        @Subsingleton.elim _ ((hdiscrete U).subsingleton X Y) _ _
      rw [hf]
      infer_instance, hfibred⟩

/-! ## The fixed-base 2-category -/

/-- The object property selecting categories fibred in sets in the fixed-base
fibred-category interface from Unit 33. -/
def IsDiscreteFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsDiscrete (Functor.Fiber (structureFunctor X.underlying) U)

def categoriesFibredInSetsObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  fun X => IsCategoryFibredInSets (structureFunctor X.underlying)

theorem discreteFibredCategoryOver_isCategoryFibredInSets
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsDiscreteFibredCategoryOver X) :
    IsCategoryFibredInSets (structureFunctor X.underlying) := by
  exact (isCategoryFibredInSets_iff_isFibered_and_discreteFibres _).mpr
    ⟨inferInstance, hX⟩

/-- The source's 2-category of categories fibred in sets over a fixed base. -/
abbrev CategoriesFibredInSetsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C)
    (categoriesFibredInSetsObjectProperty (C := C))

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

/- A vertical natural transformation between functors into a discrete fibre
   is automatically invertible.  This is the source's observation that the
   fixed-base 2-category is in fact a (2, 1)-category. -/
theorem discreteFibredCategoryOver_two_morphism_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) : IsIso η := by
  sorry

/- The stronger locally-discrete form records the source's assertion that a
   vertical 2-morphism is an identity after identifying its source and target
   1-morphisms. -/
theorem discreteFibredCategoryOver_two_morphism_is_eqToHom
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsDiscreteFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) :
    ∃ h : F = G, η = eqToHom h := by
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
  product : FibredTwoFibreProduct.{u₁, v₁, v, u} F G
  fibres_are_discrete : ∀ U : C,
    IsDiscrete (Functor.Fiber product.diagram.base U)

theorem fibredInSetsTwoFibreProduct_apex_isCategoryFibredInSets
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    {F : FibredCategoryOverHom X S} {G : FibredCategoryOverHom Y S}
    (P : FibredInSetsTwoFibreProduct F G) :
    IsCategoryFibredInSets P.product.diagram.base := by
  sorry

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
    Cᵒᵖ ⥤ Cat.{uS, uS} :=
  F ⋙ CategoryTheory.typeToCat

/-- The category `\mathcal S_F` associated to a set-valued presheaf. -/
abbrev setPresheafCategory
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :=
  groupoidPresheafCategory (setPresheafToCat F)

/-- The value of a CoGrothendieck object in the underlying set-valued
presheaf.  This is the source's displayed object `(U, x)`. -/
def setPresheafObjectValue
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    F.obj (Opposite.op X.base) :=
  Discrete.as X.fiber

@[simp]
theorem setPresheafObjectValue_mk
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) (x : F.obj (Opposite.op U)) :
    setPresheafObjectValue F
        (⟨U, Discrete.mk x⟩ : setPresheafCategory F) = x :=
  rfl

theorem setPresheaf_object_description
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    ∃ x : F.obj (Opposite.op X.base),
      X = (⟨X.base, Discrete.mk x⟩ : setPresheafCategory F) := by
  sorry

/-- The morphism with prescribed base arrow and the corresponding equality in
the set-valued presheaf.  The fibre component is the unique arrow in the
canonical discrete fibre. -/
def setPresheafHomOf
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X.base ⟶ Y.base)
    (h : F.map f.op (setPresheafObjectValue F Y) =
      setPresheafObjectValue F X) : X ⟶ Y where
  base := f
  fiber := by
    change X.fiber ⟶ Discrete.mk (F.map f.op (Discrete.as Y.fiber))
    exact Discrete.eqToHom h.symm

theorem setPresheafHom_fibre_condition
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    F.map f.base.op (setPresheafObjectValue F Y) =
      setPresheafObjectValue F X := by
  sorry

theorem setPresheafHom_exists_iff
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X.base ⟶ Y.base) :
    (∃ h : X ⟶ Y, h.base = f) ↔
      F.map f.op (setPresheafObjectValue F Y) =
        setPresheafObjectValue F X := by
  sorry

theorem setPresheaf_morphism_description
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} (f : X ⟶ Y) :
    ∃ h : F.map f.base.op (setPresheafObjectValue F Y) =
        setPresheafObjectValue F X,
      f = setPresheafHomOf F (X := X) (Y := Y) f.base h := by
  sorry

theorem setPresheafHom_ext
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y : setPresheafCategory F} {f g : X ⟶ Y}
    (h : f.base = g.base) : f = g := by
  sorry

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

@[simp]
theorem setPresheafRestriction_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) {V U : C} (f : V ⟶ U)
    (x : F.obj (Opposite.op U)) :
    (setPresheafRestriction F f).obj (Discrete.mk x) =
      Discrete.mk (F.map f.op x) :=
  rfl

theorem setPresheafRestriction_comp
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    setPresheafRestriction F (g ≫ f) =
      setPresheafRestriction F f ⋙ setPresheafRestriction F g := by
  exact groupoidPresheafRestriction_comp (setPresheafToCat F) g f

@[simp]
theorem setPresheafRestriction_id_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C)
    (x : F.obj (Opposite.op U)) :
    (setPresheafRestriction F (𝟙 U)).obj (Discrete.mk x) = Discrete.mk x := by
  change Discrete.mk (F.map (𝟙 U).op x) = Discrete.mk x
  simp

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

@[simp]
theorem setPresheaf_id_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (X : setPresheafCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem setPresheaf_comp_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y Z : setPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/- The fibre component of composition is the canonical CoGrothendieck
   composition; this is the displayed composition rule in the source. -/
theorem setPresheaf_comp_fiber
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS)
    {X Y Z : setPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((splitFibredPseudofunctor (setPresheafToCat F)).map
            f.base.op.toLoc).toFunctor.map g.fiber ≫
        ((splitFibredPseudofunctor (setPresheafToCat F)).mapComp
            g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

/- The CoGrothendieck category has the source's displayed object and
   morphism data: its objects have a base object and a value in the fibre,
   while its morphisms have a base arrow and a fibre arrow. -/
theorem setPresheaf_fibre_is_discrete
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) :
    IsDiscrete (Functor.Fiber (setPresheafProjection F) U) := by
  sorry

/- The construction is already fibred in groupoids by the generic
   CoGrothendieck lifting theorem from Unit 37.  The extra assertion here
   isolates the first part of the source's conclusion before adding the
   discrete-fibre condition. -/
theorem setPresheaf_category_isFibredInGroupoids
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    (setPresheafProjection F).IsFibredInGroupoids := by
  apply groupoidPresheafProjection_isFibredInGroupoids
  intro U
  change IsGroupoid (Discrete (F.obj (Opposite.op U)))
  infer_instance

/- The source's final conclusion combines the preceding groupoid and
   discrete-fibre assertions. -/
theorem setPresheaf_category_isFibredInSets
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) :
    IsCategoryFibredInSets (setPresheafProjection F) := by
  exact ⟨setPresheaf_category_isFibredInGroupoids F,
    setPresheaf_fibre_is_discrete F⟩

theorem setPresheaf_fibre_equivalent_to_discrete
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Type uS) (U : C) :
    Nonempty
      (Discrete (F.obj (Opposite.op U)) ≌
        Functor.Fiber (setPresheafProjection F) U) := by
  exact ⟨(Functor.Fiber.inducedFunctor
    (Pseudofunctor.CoGrothendieck.comp_const
      (splitFibredPseudofunctor (setPresheafToCat F)) U)).asEquivalence⟩

/-! ## The presheaf correspondence -/

/- The source's ordinary category of categories fibred in sets uses strict
   functors over the fixed base.  This is the full subcategory of `Over C`;
   it is distinct from the fixed-base bicategory above, whose 2-morphisms
   record the source's natural transformations over `C`. -/
def categoriesFibredInSetsOverObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (Over C) :=
  fun X => IsCategoryFibredInSets X.hom.toFunctor

abbrev CategoriesFibredInSetsOverCategory (C : Cat.{v, u}) :=
  (categoriesFibredInSetsOverObjectProperty (C := C)).FullSubcategory

theorem categoriesFibredInSetsOver_equivalent_to_presheaves
    {C : Type uC} [Category.{vC} C] :
    Nonempty
      (Presheaf C ≌
        CategoriesFibredInSetsOverCategory (Cat.of C)) := by
  sorry

/-- A chosen equivalence in the source's presheaf correspondence.  The
existence theorem above is kept as the proposition-level interface, while
this definition makes the equivalence directly usable by later statements. -/
noncomputable def categoriesFibredInSetsOverEquivalence
    {C : Type uC} [Category.{vC} C] :
    Presheaf C ≌
      CategoriesFibredInSetsOverCategory (Cat.of C) :=
  Classical.choice (categoriesFibredInSetsOver_equivalent_to_presheaves (C := C))

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

theorem sliceProjection_fibre_object_description
    {C : Type uC} [Category.{vC} C] (X U : C)
    (x : Functor.Fiber (Over.forget X) U) :
    ∃ h : U ⟶ X, x.1 = Over.mk h := by
  sorry

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
