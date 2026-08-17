import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# Categories, Chapter 2: Definitions

The source section is formalized with Mathlib's canonical category-theory
interfaces.  In particular, `Category`, `Functor`, `NatTrans`, `Equivalence`,
`Over`, `Under`, and product categories already provide the definitions in the
text.  This file records the source-facing assertions which are not merely
structure fields or existing API declarations.

The source's convention that hom-sets are disjoint is built into Lean's
dependent hom types: a morphism `X ⟶ Y` has its source and target in its type.
The list of permitted big categories, and the remarks about set-valued
functors and functors `Sets → Sets`, are universe and size guidance rather than
additional mathematical structures.  Mathlib's universe parameters and
`LargeCategory`/`SmallCategory` conventions account for that content.
-/

namespace Formalization.Books.Categories.Unit02

open CategoryTheory
open CategoryTheory.Functor

universe v u v₁ u₁ v₂ u₂ v₃ u₃

/-! ## Categories, identities, and isomorphisms -/

/- The source's identity predicate is useful for stating its uniqueness
   remark literally, while the canonical identity is `𝟙 X`. -/
def IsIdentityMorphism {C : Type u} [Category.{v} C] (X : C) (e : X ⟶ X) : Prop :=
  (∀ {Y : C} (f : X ⟶ Y), e ≫ f = f) ∧
    ∀ {Y : C} (f : Y ⟶ X), f ≫ e = f

theorem identity_morphism_unique {C : Type u} [Category.{v} C] {X : C}
    {e e' : X ⟶ X} (he : IsIdentityMorphism X e) (he' : IsIdentityMorphism X e') :
    e = e' := by
  calc
    e = e' ≫ e := (he'.1 e).symm
    _ = e' := he.2 e'

theorem isomorphism_iff_exists_inverse {C : Type u} [Category.{v} C] {X Y : C}
    (f : X ⟶ Y) :
    IsIso f ↔ ∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y := by
  constructor
  · intro h
    exact h.out
  · rintro ⟨g, hfg, hgf⟩
    exact ⟨⟨g, hfg, hgf⟩⟩

theorem inverse_morphism_unique {C : Type u} [Category.{v} C] {X Y : C}
    {f : X ⟶ Y} {g h : Y ⟶ X}
    (hg₁ : f ≫ g = 𝟙 X) (_hg₂ : g ≫ f = 𝟙 Y)
    (_hh₁ : f ≫ h = 𝟙 X) (hh₂ : h ≫ f = 𝟙 Y) :
    g = h := by
  calc
    g = 𝟙 Y ≫ g := by simp
    _ = (h ≫ f) ≫ g := by rw [hh₂]
    _ = h ≫ (f ≫ g) := by rw [Category.assoc]
    _ = h ≫ 𝟙 X := by rw [hg₁]
    _ = h := by simp

/-! ## Groupoids and the two elementary examples -/

/- A category in which all morphisms are invertible is Mathlib's
   proposition-valued `IsGroupoid` class. -/
theorem groupoid_iff_all_morphisms_invertible {C : Type u} [Category.{v} C] :
    IsGroupoid C ↔ ∀ {X Y : C} (f : X ⟶ Y), IsIso f := by
  constructor
  · rintro ⟨h⟩ X Y f
    exact h f
  · intro h
    exact ⟨fun f => h f⟩

theorem oneObjectCategoryOfGroup_has_one_object (G : Type u) [Group G] :
    ∀ x y : SingleObj G, x = y := by
  intro x y
  cases x
  cases y
  rfl

theorem oneObjectCategoryOfGroup_is_groupoid (G : Type u) [Group G] :
    IsGroupoid (SingleObj G) := by
  infer_instance

theorem oneObjectCategoryOfGroup_composition (G : Type u) [Group G]
    {x y z : SingleObj G} (f : x ⟶ y) (g : y ⟶ z) :
    f ≫ g = g * f :=
  SingleObj.comp_as_mul G f g

/- Mathlib's `SingleObj` is the canonical category with one object and
   endomorphisms given by a monoid; a group supplies the groupoid structure. -/
/- Conversely, a groupoid with one object is equivalent to the single-object
   category of the endomorphism group of that object.  The source only needs
   this up to categorical equivalence, which is the usable Lean formulation. -/
theorem one_object_groupoid_is_equivalent_to_single_object
    (C : Type u) [Category.{v} C] [IsGroupoid C] [Unique C] :
    Nonempty (C ≌ SingleObj (End (default : C))) := by
  let M := End (default : C)
  let F : C ⥤ SingleObj M :=
    { obj := fun _ => SingleObj.star M
      map := fun {X Y} f =>
        (eqToHom (Unique.eq_default X).symm ≫ f ≫ eqToHom (Unique.eq_default Y) :
          End (default : C))
      map_id := by
        intro X
        simp [M, SingleObj.id_as_one]
        exact (End.one_def (X := (default : C))).symm
      map_comp := by
        intro X Y Z f g
        cases Unique.eq_default X
        cases Unique.eq_default Y
        cases Unique.eq_default Z
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl }
  let G : SingleObj M ⥤ C :=
    SingleObj.functor (X := (default : C)) (MonoidHom.id M)
  let unitIso : 𝟭 C ≅ F ⋙ G :=
    NatIso.ofComponents (fun X => eqToIso (Unique.eq_default X)) (by
      intro X Y f
      change f ≫ eqToHom (Unique.eq_default Y) =
        eqToHom (Unique.eq_default X) ≫
          (eqToHom (Unique.eq_default X).symm ≫ f ≫ eqToHom (Unique.eq_default Y))
      simp)
  let counitIso : G ⋙ F ≅ 𝟭 (SingleObj M) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y f
      cases X
      cases Y
      simp [F, G, SingleObj.functor])
  exact ⟨Equivalence.mk' F G unitIso counitIso (by
    intro X
    cases Unique.eq_default X
    simp [M, F, G, unitIso, counitIso, SingleObj.functor, SingleObj.id_as_one]
    exact Category.id_comp (1 : End (default : C)))⟩

theorem discreteCategoryOn_is_groupoid (C : Type u) :
    IsGroupoid (Discrete C) := by
  infer_instance

theorem discreteCategoryOn_hom_subsingleton (C : Type u)
    (x y : Discrete C) :
    Subsingleton (x ⟶ y) := by
  infer_instance

theorem discreteCategoryOn_hom_nonempty_iff (C : Type u)
    (x y : Discrete C) :
    Nonempty (x ⟶ y) ↔ x.as = y.as := by
  constructor
  · rintro ⟨f⟩
    exact Discrete.eq_of_hom f
  · intro h
    exact ⟨Discrete.eqToHom h⟩

theorem discreteCategoryOn_identity_is_unique (C : Type u)
    (x : Discrete C) (f : x ⟶ x) :
    f = 𝟙 x := by
  exact Subsingleton.elim _ _

/-! ## Functors and their standard properties -/

theorem functor_preserves_identity {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    F.map (𝟙 X) = 𝟙 (F.obj X) :=
  F.map_id X

theorem functor_preserves_composition {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (f ≫ g) = F.map f ≫ F.map g :=
  F.map_comp f g

theorem faithful_iff_injective_maps
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    F.Faithful ↔
      ∀ (X Y : C), Function.Injective
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  constructor
  · rintro ⟨h⟩ X Y
    exact h
  · intro h
    exact ⟨fun {_ _} => h _ _⟩

theorem full_iff_surjective_maps
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    F.Full ↔
      ∀ (X Y : C), Function.Surjective
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  constructor
  · rintro ⟨h⟩ X Y
    exact h
  · intro h
    exact ⟨fun {_ _} => h _ _⟩

/- Mathlib's `Full` and `Faithful` are the source's full and faithful
   conditions.  `FullyFaithful` packages the resulting hom-set bijections. -/
theorem fully_faithful_iff_bijective_maps
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    Nonempty F.FullyFaithful ↔
      ∀ (X Y : C), Function.Bijective
        (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  Functor.FullyFaithful.nonempty_iff_map_bijective F

theorem essentially_surjective_iff_isomorphic_preimages
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    F.EssSurj ↔ ∀ Y : D, ∃ X : C, Nonempty (F.obj X ≅ Y) := by
  constructor
  · intro h Y
    let _ : F.EssSurj := h
    simpa [Functor.essImage] using
      (Functor.EssSurj.mem_essImage (F := F) Y)
  · intro h
    exact
      { mem_essImage := fun Y => by
          simpa [Functor.essImage] using h Y }

theorem groupHomomorphismFunctor_faithful_iff_injective
    {G : Type u} {H : Type v} [Group G] [Group H] (p : G →* H) :
    (MonoidHom.toFunctor p).Faithful ↔ Function.Injective p := by
  rw [faithful_iff_injective_maps]
  change (∀ (X Y : SingleObj G), Function.Injective p) ↔ Function.Injective p
  exact ⟨fun h => h (SingleObj.star G) (SingleObj.star G), fun h _ _ => h⟩

theorem groupHomomorphismFunctor_fully_faithful_iff_bijective
    {G : Type u} {H : Type v} [Group G] [Group H] (p : G →* H) :
    Nonempty (MonoidHom.toFunctor p).FullyFaithful ↔ Function.Bijective p := by
  rw [fully_faithful_iff_bijective_maps]
  change (∀ (X Y : SingleObj G), Function.Bijective p) ↔ Function.Bijective p
  exact ⟨fun h => h (SingleObj.star G) (SingleObj.star G), fun h _ _ => h⟩

/-! ## Subcategories -/

/- Mathlib does not introduce a separate strict-full subcategory structure;
   closure of the object property under isomorphisms is the source's
   strict-full condition for `ObjectProperty.FullSubcategory`. -/
abbrev StrictlyFullObjectProperty {C : Type u} [Category.{v} C]
    (P : ObjectProperty C) : Prop :=
  ObjectProperty.IsClosedUnderIsomorphisms P

abbrev full_subcategory_inclusion_is_fully_faithful
    {C : Type u} [Category.{v} C] (P : ObjectProperty C) :
    P.ι.FullyFaithful :=
  P.fullyFaithfulι

theorem full_subcategory_inclusion_is_full_and_faithful
    {C : Type u} [Category.{v} C] (P : ObjectProperty C) :
    P.ι.Full ∧ P.ι.Faithful := by
  exact ⟨inferInstance, inferInstance⟩

/-! ## Over and under categories -/

theorem over_category_forget_object {C : Type u} [Category.{v} C] {X : C}
    (U : Over X) :
    (Over.forget X).obj U = U.left :=
  Over.forget_obj

theorem over_category_reindexing_object_hom {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ X) :
    ((Over.map f).obj (Over.mk g)).hom = g ≫ f := by
  exact Over.map_obj_hom

theorem over_category_reindexing_forget {C : Type u} [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) :
    (Over.map f) ⋙ (Over.forget Y) = Over.forget X :=
  Over.mapForget_eq f

theorem under_category_forget_object {C : Type u} [Category.{v} C] {X : C}
    (U : Under X) :
    (Under.forget X).obj U = U.right :=
  Under.forget_obj

theorem under_category_reindexing_object_hom {C : Type u} [Category.{v} C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((Under.map f).obj (Under.mk g)).hom = f ≫ g := by
  exact Under.map_obj_hom

theorem under_category_reindexing_forget {C : Type u} [Category.{v} C]
    {X Y : C} (f : X ⟶ Y) :
    (Under.map f) ⋙ (Under.forget X) = Under.forget Y :=
  Under.mapForget_eq f

/-! ## Natural transformations and functor categories -/

/- Mathlib's `Functor.category` instance equips `C ⥤ D` with the category of
   natural transformations described in the source. -/
theorem natural_transformation_naturality
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G : C ⥤ D} (t : F ⟶ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ t.app Y = t.app X ≫ G.map f :=
  t.naturality f

theorem natural_transformation_identity_component
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (X : C) :
    (NatTrans.id F).app X = 𝟙 (F.obj X) :=
  NatTrans.id_app' F X

theorem natural_transformation_composition_component
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G H : C ⥤ D} (s : F ⟶ G) (t : G ⟶ H) (X : C) :
    (s ≫ t).app X = s.app X ≫ t.app X := by
  rfl

/-! ## Equivalences of categories -/

theorem functor_is_equivalence_iff_quasi_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    F.IsEquivalence ↔
      ∃ G : D ⥤ C,
        Nonempty (𝟭 C ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 D) := by
  constructor
  · intro h
    let _ : F.IsEquivalence := h
    let e := F.asEquivalence
    exact ⟨e.inverse, ⟨e.unitIso⟩, ⟨e.counitIso⟩⟩
  · rintro ⟨G, ⟨unitIso⟩, ⟨counitIso⟩⟩
    exact Functor.IsEquivalence.mk' G unitIso counitIso

/- The source chooses an object `j(X)` and an isomorphism
   `X ≅ F(j(X))`.  `HEq` records the component equality while allowing a
   functor whose object function is propositionally equal to that chosen rule. -/
theorem construct_quasi_inverse
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) [F.Full] [F.Faithful]
    (jObj : D → C) (i : ∀ X : D, X ≅ F.obj (jObj X)) :
    ∃! (j : D ⥤ C),
      (∀ X : D, j.obj X = jObj X) ∧
      (∃ t : 𝟭 D ≅ j ⋙ F, ∀ X : D, HEq (t.app X) (i X)) ∧
      ∃ e : C ≌ D, e.functor = F ∧ e.inverse = j := by
  let j : D ⥤ C :=
    { obj := jObj
      map := fun {X Y} f => F.preimage ((i X).inv ≫ f ≫ (i Y).hom)
      map_id := by
        intro X
        apply F.map_injective
        simp
      map_comp := by
        intro X Y Z f g
        apply F.map_injective
        simp }
  let t : 𝟭 D ≅ j ⋙ F :=
    NatIso.ofComponents i (by
      intro X Y f
      simp [j])
  let u : 𝟭 C ≅ F ⋙ j :=
    NatIso.ofComponents (fun X => F.preimageIso (i (F.obj X))) (by
      intro X Y f
      apply F.map_injective
      simp [j, Functor.preimageIso])
  let e : C ≌ D :=
    Equivalence.mk' F j u t.symm (by
      intro X
      simp [u, t, j, Functor.preimageIso])
  refine ⟨j, ?_, ?_⟩
  · refine ⟨fun X => rfl, ⟨t, ?_⟩, ⟨e, rfl, rfl⟩⟩
    intro X
    rfl
  · rintro j' ⟨hObj, ⟨t', ht'⟩, e', hFunctor, hInverse⟩
    have hObjFun : j'.obj = jObj := funext hObj
    cases j' with
    | mk obj' map' map_id' map_comp' =>
      dsimp at hObjFun
      cases hObjFun
      dsimp [j]
      refine Functor.hext
        (F := { obj := jObj, map := map', map_id := map_id', map_comp := map_comp' })
        (G := j) (fun _ => rfl) ?_
      intro X Y f
      apply heq_of_eq
      apply F.map_injective
      have hnat' := t'.hom.naturality f
      have hnat := t.hom.naturality f
      have hX : t'.hom.app X = (i X).hom := by
        change (t'.app X).hom = (i X).hom
        exact congrArg Iso.hom (eq_of_heq (ht' X))
      have hY : t'.hom.app Y = (i Y).hom := by
        change (t'.app Y).hom = (i Y).hom
        exact congrArg Iso.hom (eq_of_heq (ht' Y))
      rw [hX, hY] at hnat'
      apply (cancel_epi (i X).hom).1
      exact hnat'.symm.trans hnat

theorem equivalence_iff_full_faithful_essentially_surjective
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) :
    F.IsEquivalence ↔ F.Full ∧ F.Faithful ∧ F.EssSurj := by
  constructor
  · intro h
    exact ⟨h.full, h.faithful, h.essSurj⟩
  · rintro ⟨hFull, hFaithful, hEssSurj⟩
    exact { full := hFull, faithful := hFaithful, essSurj := hEssSurj }

/-! ## Product categories -/

/- The category instance on `C × D` is Mathlib's componentwise product
   category. -/
theorem product_category_identity
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (X : C) (Y : D) :
    𝟙 (X, Y) = (𝟙 X, 𝟙 Y) := by
  rfl

theorem product_category_composition
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {X X' X'' : C} {Y Y' Y'' : D}
    (f : (X, Y) ⟶ (X', Y')) (g : (X', Y') ⟶ (X'', Y'')) :
    f ≫ g = (f.1 ≫ g.1, f.2 ≫ g.2) := by
  rfl

end Formalization.Books.Categories.Unit02
