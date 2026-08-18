import Formalization.Books.Categories.Unit35.CategoriesFibredInGroupoids
import Formalization.Books.Categories.Unit36.PresheavesOfCategories

/-!
# Categories, Chapter 37: Presheaves of groupoids

The source compares categories fibred in groupoids with functors to the
2-category of groupoids.  The groupoid 2-category is the full sub-2-category
of `Cat` from Unit 29, and the associated fibred category is Mathlib's
CoGrothendieck construction, as in Unit 36.
-/

namespace Formalization.Books.Categories.Unit37

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open Opposite
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit35
open Formalization.Books.Categories.Unit36

universe vC uC vG uG vS uS

noncomputable section

variable {C : Type uC} [Category.{vC} C]

/-! ## Groupoid-valued presheaves -/

/- A functor `Cᵒᵖ ⥤ Cat` together with the assertion that each value is a
groupoid is the underlying-functor presentation of Unit 29's full
sub-2-category of groupoids.  The declarations below keep the property as an
explicit hypothesis so that the canonical `Cat`-valued construction from
Unit 36 can be reused without introducing another category of groupoids. -/

/-- The underlying `Cat`-valued functor of a groupoid-valued presheaf. -/
abbrev groupoidPresheafToCat
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG}) :
    Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG} :=
  F

/-! ## The associated fibred category -/

/-- The category `\mathcal S_F` associated to a groupoid-valued presheaf. -/
abbrev groupoidPresheafCategory
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG}) :=
  splitFibredCategory (groupoidPresheafToCat F)

/-- The projection `p_F : \mathcal S_F ⥤ C`. -/
abbrev groupoidPresheafProjection
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG}) :
    groupoidPresheafCategory F ⥤ C :=
  splitFibredProjection (groupoidPresheafToCat F)

/-- An object of `\mathcal S_F`, displayed as a base object and an object in
the corresponding groupoid. -/
abbrev groupoidPresheafObject
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG}) :=
  groupoidPresheafCategory F

/-- A morphism of `\mathcal S_F`, displayed as a base arrow and a fibre arrow. -/
abbrev groupoidPresheafHom
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {X Y : groupoidPresheafCategory F} :=
  splitFibredHom (groupoidPresheafToCat F) (X := X) (Y := Y)

/-- The restriction functor `f^*` attached to a base arrow `f : V ⟶ U`. -/
abbrev groupoidPresheafRestriction
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {V U : C} (f : V ⟶ U) :
    (groupoidPresheafToCat F).obj (Opposite.op U) ⥤
      (groupoidPresheafToCat F).obj (Opposite.op V) :=
  splitRestriction (groupoidPresheafToCat F) f

theorem groupoidPresheafRestriction_comp
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    groupoidPresheafRestriction F (g ≫ f) =
      groupoidPresheafRestriction F f ⋙ groupoidPresheafRestriction F g := by
  exact splitRestriction_comp (groupoidPresheafToCat F) g f

@[simp]
theorem groupoidPresheafProjection_obj
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    (X : groupoidPresheafCategory F) :
    (groupoidPresheafProjection F).obj X = X.base :=
  rfl

@[simp]
theorem groupoidPresheafProjection_map
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {X Y : groupoidPresheafCategory F} (f : X ⟶ Y) :
    (groupoidPresheafProjection F).map f = f.base :=
  rfl

@[simp]
theorem groupoidPresheaf_id_base
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    (X : groupoidPresheafCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem groupoidPresheaf_comp_base
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {X Y Z : groupoidPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/- The source's composition rule is the fibre component of the canonical
CoGrothendieck composition. -/
theorem groupoidPresheaf_comp_fiber
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {X Y Z : groupoidPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((splitFibredPseudofunctor (groupoidPresheafToCat F)).map
            f.base.op.toLoc).toFunctor.map g.fiber ≫
        ((splitFibredPseudofunctor (groupoidPresheafToCat F)).mapComp
            g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

/-- The canonical lift of `f : V ⟶ U` with codomain `(U, x)` is
`(f, id_{f^* x})`. -/
abbrev groupoidPresheafCartesianDomain
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {V U : C} (f : V ⟶ U)
    (x : (groupoidPresheafToCat F).obj (Opposite.op U)) :
    groupoidPresheafCategory F :=
  splitFibredCartesianDomain (groupoidPresheafToCat F) f x

abbrev groupoidPresheafCartesianLift
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {V U : C} (f : V ⟶ U)
    (x : (groupoidPresheafToCat F).obj (Opposite.op U)) :
    groupoidPresheafCartesianDomain F f x ⟶
      (⟨U, x⟩ : groupoidPresheafCategory F) :=
  splitFibredCartesianLift (groupoidPresheafToCat F) f x

theorem groupoidPresheafCartesianLift_isHomLift
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {V U : C} (f : V ⟶ U)
    (x : (groupoidPresheafToCat F).obj (Opposite.op U)) :
    (groupoidPresheafProjection F).IsHomLift f
      (groupoidPresheafCartesianLift F f x) := by
  exact splitFibredCartesianLift_isHomLift (groupoidPresheafToCat F) f x

theorem groupoidPresheaf_exists_lift
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {V U : C} (f : V ⟶ U)
    (x : (groupoidPresheafToCat F).obj (Opposite.op U)) :
    ∃ (y : groupoidPresheafCategory F) (φ : y ⟶ (⟨U, x⟩ : groupoidPresheafCategory F)),
      (groupoidPresheafProjection F).IsHomLift f φ := by
  exact ⟨groupoidPresheafCartesianDomain F f x,
    groupoidPresheafCartesianLift F f x,
    groupoidPresheafCartesianLift_isHomLift F f x⟩

theorem groupoidPresheafProjection_isFibered
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG}) :
    (groupoidPresheafProjection F).IsFibered := by
  exact splitFibredProjection_isFibered (groupoidPresheafToCat F)

private theorem groupoidPresheaf_fibre_is_groupoid_aux
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    (hF : ∀ U : C, IsGroupoid (F.obj (Opposite.op U))) (U : C) :
    IsGroupoid (Functor.Fiber (groupoidPresheafProjection F) U) := by
  let e := HasFibers.inducedFunctor (groupoidPresheafProjection F) U
  letI : IsGroupoid (F.obj (Opposite.op U)) := hF U
  exact isGroupoid_of_reflects_iso e.inv

/-- The groupoid-valued construction has groupoid fibres and satisfies the
two lifting conditions for a category fibred in groupoids. -/
theorem groupoidPresheafProjection_isFibredInGroupoids
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    (hF : ∀ U : C, IsGroupoid (F.obj (Opposite.op U))) :
    (groupoidPresheafProjection F).IsFibredInGroupoids := by
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres
    (groupoidPresheafProjection F)).mpr
  constructor
  · exact groupoidPresheaf_fibre_is_groupoid_aux F hF
  · exact groupoidPresheafProjection_isFibered F

theorem groupoidPresheaf_fibre_is_groupoid
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    (hF : ∀ U : C, IsGroupoid (F.obj (Opposite.op U))) (U : C) :
    IsGroupoid (Functor.Fiber (groupoidPresheafProjection F) U) := by
  exact groupoidPresheaf_fibre_is_groupoid_aux F hF U

theorem groupoidPresheaf_unique_lift
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vG, uG})
    {x y z : groupoidPresheafCategory F} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : (groupoidPresheafProjection F).obj z ⟶
      (groupoidPresheafProjection F).obj y}
    (hp : (groupoidPresheafProjection F).IsFibredInGroupoids)
    (h : f ≫ (groupoidPresheafProjection F).map φ =
      (groupoidPresheafProjection F).map ψ) :
    ∃! χ : z ⟶ y,
      (groupoidPresheafProjection F).IsHomLift f χ ∧ χ ≫ φ = ψ := by
  exact hp.unique_lift φ ψ h

/-! ## Split categories fibred in groupoids -/

/-- A category fibred in groupoids is split when it is isomorphic over its
base to a groupoid-valued presheaf construction. -/
def IsSplitCategoryFibredInGroupoids
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧
    ∃ (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vS, uS}),
      (∀ U : C, IsGroupoid (F.obj (Opposite.op U))) ∧
        IsomorphicOverBase p (groupoidPresheafProjection F)

theorem groupoidPresheafProjection_isSplit
    (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vS, uS})
    (hF : ∀ U : C, IsGroupoid (F.obj (Opposite.op U))) :
    IsSplitCategoryFibredInGroupoids (groupoidPresheafProjection F) := by
  refine ⟨groupoidPresheafProjection_isFibredInGroupoids F hF, F, hF, ?_⟩
  exact ⟨𝟭 _, 𝟭 _, Functor.id_comp _, Functor.id_comp _,
    Functor.id_comp _, Functor.id_comp _⟩

/-! ## Every category fibred in groupoids is equivalent to a split one -/

/-- The strictification category in the proof is the generic category from
Unit 36: its objects are pairs `(x, f : V ⟶ U)`, and its morphisms are the
underlying arrows between the chosen pullbacks. -/
abbrev groupoidStrictificationCategory
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :=
  StrictificationCategory p P

abbrev groupoidStrictificationProjection
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    groupoidStrictificationCategory P ⥤ C :=
  strictificationProjection P

theorem groupoidStrictificationProjection_isFibredInGroupoids
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered]
    (hp : p.IsFibredInGroupoids) (P : PullbackChoice p) :
    (groupoidStrictificationProjection P).IsFibredInGroupoids := by
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres
    (groupoidStrictificationProjection P)).mpr
  constructor
  · intro U
    constructor
    intro X Y f
    let _ : (groupoidStrictificationProjection P).IsHomLift
        (𝟙 U) f.1 := f.2
    have hmap : IsIso (p.map f.1.hom) := by
      let hd := CategoryTheory.IsHomLift.domain_eq
        (groupoidStrictificationProjection P) (𝟙 U) f.1
      let hc := CategoryTheory.IsHomLift.codomain_eq
        (groupoidStrictificationProjection P) (𝟙 U) f.1
      letI : IsIso (eqToHom hd) := (eqToIso hd).isIso_hom
      letI : IsIso (eqToHom hc.symm) := (eqToIso hc.symm).isIso_hom
      have h := CategoryTheory.IsHomLift.fac'
        (groupoidStrictificationProjection P) (𝟙 U) f.1
      change p.map f.1.hom = _ at h
      rw [h]
      simp only [Category.id_comp]
      exact IsIso.comp_isIso' (eqToIso hd).isIso_hom
        (eqToIso hc.symm).isIso_hom
    let _ : IsIso (p.map f.1.hom) := hmap
    let _ : p.IsStronglyCartesian (p.map f.1.hom) f.1.hom :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p hp f.1.hom
    let _ : IsIso f.1.hom :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso p
        (p.map f.1.hom) f.1.hom
    let e : X.1 ≅ Y.1 where
      hom := { hom := f.1.hom }
      inv := { hom := inv f.1.hom }
      hom_inv_id := by
        apply StrictificationHom.ext
        simp
      inv_hom_id := by
        apply StrictificationHom.ext
        simp
    have hehom : e.hom = f.1 := by
      apply StrictificationHom.ext
      rfl
    let _ : (groupoidStrictificationProjection P).IsHomLift
        (𝟙 U) e.hom := by
      rw [hehom]
      exact f.2
    have hinv : (groupoidStrictificationProjection P).IsHomLift
        (𝟙 U) e.inv :=
      CategoryTheory.IsHomLift.lift_id_inv
        (groupoidStrictificationProjection P) U e
    exact ⟨⟨e.inv, hinv⟩, by
      constructor
      · apply Functor.Fiber.hom_ext
        change f.1 ≫ e.inv = 𝟙 X.1
        rw [← hehom]
        exact e.hom_inv_id
      · apply Functor.Fiber.hom_ext
        change e.inv ≫ f.1 = 𝟙 Y.1
        rw [← hehom]
        exact e.inv_hom_id⟩
  · exact strictificationProjection_isFibered P

theorem fibred_groupoids_equivalent_to_split
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    ∃ (F : Cᵒᵖ ⥤ CategoryTheory.Cat.{vS, uS}),
      (∀ U : C, IsGroupoid (F.obj (Opposite.op U))) ∧
        IsFibredEquivalenceOver p (groupoidPresheafProjection F) := by
  letI : p.IsFibered :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp
      (inferInstance : p.IsFibredInGroupoids) |>.2
  obtain ⟨F, hEq⟩ := fibred_category_equivalent_to_split p
  rcases hEq with ⟨K, G, hK, hG, hKcart, hGcart,
    ⟨eKG, overKG, hOverKG⟩, ⟨eGK, overGK, hOverGK⟩⟩
  letI : G.IsEquivalence :=
    Functor.IsEquivalence.mk' K eGK.symm eKG
  let q := groupoidPresheafProjection F
  have hqgroup : ∀ U : C, IsGroupoid (Functor.Fiber q U) := by
    intro U
    constructor
    intro X Y f
    let _ : q.IsHomLift (𝟙 U) f.1 := f.2
    have hqmap : IsIso (q.map f.1) := by
      rw [CategoryTheory.IsHomLift.fac' q (𝟙 U) f.1]
      infer_instance
    have hGmap : p.map (G.map f.1) = q.map f.1 := by
      simpa [q] using Functor.congr_hom hG f.1
    let _ : IsIso (p.map (G.map f.1)) := by
      rw [hGmap]
      exact hqmap
    let _ : p.IsStronglyCartesian (p.map (G.map f.1)) (G.map f.1) :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p
        (inferInstance : p.IsFibredInGroupoids) (G.map f.1)
    let _ : IsIso (G.map f.1) :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso p
        (p.map (G.map f.1)) (G.map f.1)
    let _ : IsIso f.1 := isIso_of_reflects_iso f.1 G
    let e : X.1 ≅ Y.1 := asIso f.1
    let _ : q.IsHomLift (𝟙 U) e.hom := by
      dsimp [e]
      exact f.2
    have hinv : q.IsHomLift (𝟙 U) e.inv :=
      CategoryTheory.IsHomLift.lift_id_inv q U e
    let e' : X ≅ Y where
      hom := ⟨e.hom, inferInstance⟩
      inv := ⟨e.inv, hinv⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id
    exact ⟨⟨e'⟩⟩
  have hF : ∀ U : C, IsGroupoid (F.obj (Opposite.op U)) := by
    intro U
    let e := HasFibers.inducedFunctor q U
    letI : IsGroupoid (Functor.Fiber q U) := hqgroup U
    exact isGroupoid_of_reflects_iso e
  refine ⟨F, hF, ?_⟩
  exact ⟨K, G, hK, hG, hKcart, hGcart,
    ⟨eKG, overKG, hOverKG⟩, ⟨eGK, overGK, hOverGK⟩⟩

end

end Formalization.Books.Categories.Unit37
