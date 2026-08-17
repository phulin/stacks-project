import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.InducedBicategory
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Categories, Chapter 29: 2-categories

The source uses strict 2-categories.  Mathlib's `Bicategory` contains the
objects, hom-categories, whiskering, and coherence data, while
`Bicategory.Strict` records the strict associativity and unit laws.  This
file uses those canonical interfaces and only adds the source-facing
operations and predicates needed below.
-/

namespace Formalization.Books.Categories.Unit29

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.ObjectProperty

universe w v u w' v' u' wC vC uC

/-! ## Strict 2-categories -/

/-- The source's strict 2-category condition is Mathlib's `Bicategory.Strict`.

The underlying `Bicategory` supplies the object type, the categories of
1-morphisms and 2-morphisms, vertical composition, whiskering, and the
interchange law.  `Bicategory.Strict` adds the ordinary category laws for
1-morphism composition and identifies the associators and unitors with the
corresponding equality isomorphisms.
-/
abbrev IsStrictTwoCategory (C : Type u) [Bicategory.{w, v} C] : Prop :=
  Bicategory.Strict C

/-- Horizontal composition of 2-morphisms, with the outer 2-morphism first.

Thus `horizontalComposition β α` is the source's `β ⋆ α`: if `α` is a
2-morphism between `f` and `f'`, and `β` is a 2-morphism between `g` and `g'`,
the result is a 2-morphism between `f ≫ g` and `f' ≫ g'`.  The definition is
the canonical pasting of right and left whiskering.
-/
def horizontalComposition {C : Type u} [Bicategory.{w, v} C]
    {a b c : C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (β : g ⟶ g') (α : f ⟶ f') : f ≫ g ⟶ f' ≫ g' :=
  Bicategory.whiskerRight α g ≫ Bicategory.whiskerLeft f' β

/- The functor in the source definition gives both identities and
   interchange for horizontal composition. -/
theorem horizontalComposition_identity {C : Type u} [Bicategory.{w, v} C]
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    horizontalComposition (𝟙 g) (𝟙 f) = 𝟙 (f ≫ g) := by
  simp [horizontalComposition]

theorem horizontalComposition_interchange {C : Type u} [Bicategory.{w, v} C]
    {a b c : C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (β₁ : g₁ ⟶ g₂) (β₂ : g₂ ⟶ g₃)
    (α₁ : f₁ ⟶ f₂) (α₂ : f₂ ⟶ f₃) :
    horizontalComposition (β₁ ≫ β₂) (α₁ ≫ α₂) =
      horizontalComposition β₁ α₁ ≫ horizontalComposition β₂ α₂ := by
  simp only [horizontalComposition, Bicategory.comp_whiskerRight,
    Bicategory.whiskerLeft_comp, Category.assoc]
  rw [Bicategory.whisker_exchange_assoc α₂ β₁]

theorem horizontalComposition_associative {C : Type u}
    [Bicategory.{w, v} C] [Bicategory.Strict C]
    {a b c d : C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (γ : h ⟶ h') (β : g ⟶ g') (α : f ⟶ f') :
    HEq (horizontalComposition (horizontalComposition γ β) α)
      (horizontalComposition γ (horizontalComposition β α)) := by
  simp [horizontalComposition, Bicategory.Strict.associator_eqToIso]
  congr 1
  · simp
  · simp
    simpa only [Category.assoc] using
      (comp_eqToHom_heq (f' ◁ β ▷ h ≫ f' ◁ g' ◁ γ)
        (Bicategory.Strict.assoc f' g' h').symm).symm

theorem horizontalComposition_left_identity {C : Type u}
    [Bicategory.{w, v} C] [Bicategory.Strict C]
    {a b : C} {f f' : a ⟶ b} (α : f ⟶ f') :
    HEq (horizontalComposition (𝟙 (𝟙 b)) α) α := by
  simp [horizontalComposition, Bicategory.Strict.rightUnitor_eqToIso]

theorem horizontalComposition_right_identity {C : Type u}
    [Bicategory.{w, v} C] [Bicategory.Strict C]
    {a b : C} {g g' : a ⟶ b} (β : g ⟶ g') :
    HEq (horizontalComposition β (𝟙 (𝟙 a))) β := by
  simp [horizontalComposition, Bicategory.Strict.leftUnitor_eqToIso]

/-- The functor of 1-morphism composition from the source definition.

Its source is ordered as `(outer 1-morphism, inner 1-morphism)`, so its object
map sends `(g, f)` to `f ≫ g` and its morphism map is
`horizontalComposition`. -/
def compositionFunctor {C : Type u} [Bicategory.{w, v} C]
    {a b c : C} :
    (b ⟶ c) × (a ⟶ b) ⥤ (a ⟶ c) where
  obj p := p.2 ≫ p.1
  map {_ _} k := horizontalComposition k.1 k.2
  map_id p := horizontalComposition_identity p.2 p.1
  map_comp k l := horizontalComposition_interchange k.1 l.1 k.2 l.2

/-! ## Sub-2-categories and large examples -/

/-- An embedding presentation of a sub-2-category.

The carrier `D` has its own strict 2-category structure, while `inclusion`
embeds its objects, 1-morphisms, and 2-morphisms into `C` and preserves the
strict operations.  The injectivity fields express that the chosen data are
subsets/subcategories of the ambient data.  This is the non-full generality
of the source definition; `FullSubTwoCategory` below is the canonical full
case supplied by Mathlib.
-/
structure SubTwoCategory (D : Type u') [Bicategory.{w', v'} D]
    [Bicategory.Strict D] (C : Type u) [Bicategory.{w, v} C]
    [Bicategory.Strict C] where
  inclusion : StrictPseudofunctor D C
  obj_injective : Function.Injective inclusion.obj
  map_injective : ∀ {x y : D},
    Function.Injective (inclusion.map : (x ⟶ y) → (inclusion.obj x ⟶ inclusion.obj y))
  map₂_injective : ∀ {x y : D} {f g : x ⟶ y},
    Function.Injective
      (inclusion.map₂ : (f ⟶ g) → (inclusion.map f ⟶ inclusion.map g))

/-- Proposition-valued form of the sub-2-category interface. -/
abbrev IsSubTwoCategory (D : Type u') [Bicategory.{w', v'} D]
    [Bicategory.Strict D] (C : Type u) [Bicategory.{w, v} C]
    [Bicategory.Strict C] : Prop :=
  Nonempty (SubTwoCategory D C)

/-- The full sub-2-category on an object property.

This is Mathlib's canonical `InducedBicategory`; its hom-categories contain
all ambient 1- and 2-morphisms between selected objects.  It is the
full-on-homs instance of the source's sub-2-category definition, and is the
interface used for the standard examples in this chapter.
-/
abbrev FullSubTwoCategory (C : Type uC) [Bicategory.{wC, vC} C]
    [Bicategory.Strict C]
    (P : ObjectProperty C) :=
  Bicategory.InducedBicategory C P.ι.obj

theorem fullSubTwoCategory_is_strict {C : Type uC} [Bicategory.{wC, vC} C]
    [Bicategory.Strict C] (P : ObjectProperty C) :
    Bicategory.Strict (FullSubTwoCategory C P) := by
  infer_instance

/-- The strict pseudofunctor which includes a full sub-2-category. -/
abbrev fullSubTwoCategory_inclusion {C : Type uC} [Bicategory.{wC, vC} C]
    [Bicategory.Strict C]
    (P : ObjectProperty C) :
    StrictPseudofunctor (FullSubTwoCategory C P) C :=
  Bicategory.InducedBicategory.forget (C := C) (F := P.ι.obj)

theorem fullSubTwoCategory_is_subTwoCategory {C : Type uC}
    [Bicategory.{wC, vC} C] [Bicategory.Strict C]
    (P : ObjectProperty C) :
    IsSubTwoCategory (FullSubTwoCategory C P) C := by
  refine ⟨SubTwoCategory.mk (fullSubTwoCategory_inclusion P) ?_ ?_ ?_⟩
  · intro X Y h
    cases X
    cases Y
    cases h
    rfl
  · intro X Y f g h
    exact Bicategory.InducedBicategory.hom_ext h
  · intro X Y f g η θ h
    exact Bicategory.InducedBicategory.hom₂_ext h

/- The source permits large object collections.  Mathlib represents each
   universe-bounded collection by a type, and `Cat` is the standard
   universe-bounded category of categories. -/
theorem categories_form_a_strict_two_category :
    Bicategory.Strict (CategoryTheory.Cat.{v, u}) := by
  infer_instance

theorem categories_two_one_is_locally_groupoid :
    Bicategory.IsLocallyGroupoid (Bicategory.Pith (CategoryTheory.Cat.{v, u})) := by
  infer_instance

/-- The universe-bounded 2-category of groupoids as a full sub-2-category of `Cat`.

Its objects are categories carrying an `IsGroupoid` instance; the selected
1-morphisms and 2-morphisms are the ambient functors and natural
transformations.
-/
def groupoidObjectProperty : ObjectProperty (CategoryTheory.Cat.{v, u}) :=
  fun C => IsGroupoid C

theorem groupoids_form_a_strict_two_category :
    Bicategory.Strict
      (FullSubTwoCategory (CategoryTheory.Cat.{v, u}) groupoidObjectProperty) := by
  infer_instance

theorem groupoids_form_a_two_one_category :
    Bicategory.IsLocallyGroupoid
      (FullSubTwoCategory (CategoryTheory.Cat.{v, u}) groupoidObjectProperty) := by
  intro X Y
  refine ⟨fun {f g} η => ?_⟩
  have h : ∀ Z : X.obj, IsIso (η.hom.toNatTrans.app Z) :=
    fun Z => Y.property.all_isIso _
  let e : f.hom ≅ g.hom :=
    Cat.Hom.isoMk
      (NatIso.ofComponents
        (fun Z => @asIso _ _ _ _ (η.hom.toNatTrans.app Z) (h Z))
        (by
          intro A B k
          change f.hom.toFunctor.map k ≫ _ = _ ≫ g.hom.toFunctor.map k
          exact η.hom.toNatTrans.naturality k))
  have he : e.hom = η.hom := by
    apply Cat.Hom₂.ext
    ext Z
    simp [e]
  refine ⟨⟨e.inv⟩, ?_, ?_⟩
  · apply Bicategory.InducedBicategory.hom₂_ext
    change η.hom ≫ e.inv = 𝟙 f.hom
    rw [← he]
    exact e.hom_inv_id
  · apply Bicategory.InducedBicategory.hom₂_ext
    change e.inv ≫ η.hom = 𝟙 g.hom
    rw [← he]
    exact e.inv_hom_id

/- The remaining entries in the source's list (fibred categories and the
   various kinds of stacks) are later constructions.  Their 2-categories fit
   the same `SubTwoCategory`/`FullSubTwoCategory` pattern once those carriers
   are defined; this chapter introduces no such carrier. -/

/-! ## Equivalence of objects -/

/-- The source's equivalence relation on objects of a 2-category.

Mathlib composes 1-morphisms from left to right.  Consequently the source's
`F ∘ G` is represented by `G ≫ F`, and the source's `G ∘ F` by `F ≫ G`.
-/
def TwoCategoryEquivalent {C : Type u} [Bicategory.{w, v} C]
    (x y : C) : Prop :=
  ∃ (F : x ⟶ y) (G : y ⟶ x),
    Nonempty (G ≫ F ≅ 𝟙 y) ∧ Nonempty (F ≫ G ≅ 𝟙 x)

/-! ## Functors from ordinary categories -/

/-- An ordinary functor into a strict 2-category, which forgets 2-morphisms.

The category instance on `C` is Mathlib's `StrictBicategory.category`.
-/
abbrev FunctorIntoTwoCategory (A : Type u') [Category.{v'} A]
    (C : Type u) [Bicategory.{w, v} C] [Bicategory.Strict C] :=
  A ⥤ C

/-! ## Pseudofunctors from ordinary categories -/

/-- A pseudofunctor from an ordinary category is a pseudofunctor from its
locally discrete bicategory. -/
abbrev PseudofunctorFromCategory (A : Type u') [Category.{v'} A]
    (C : Type u) [Bicategory.{w, v} C] :=
  Pseudofunctor (LocallyDiscrete A) C

section PseudofunctorsFromCategories

variable {A : Type u'} [Category.{v'} A]
variable {C : Type u} [Bicategory.{w, v} C]

/-- The canonical pseudofunctor associated to an ordinary functor into a
strict 2-category. -/
abbrev ordinaryFunctorToPseudofunctor [Bicategory.Strict C]
    (F : FunctorIntoTwoCategory A C) : PseudofunctorFromCategory A C :=
  F.toPseudofunctor'

/-- The object part of a pseudofunctor from an ordinary category. -/
abbrev pseudofunctorObject (F : PseudofunctorFromCategory A C) (X : A) : C :=
  F.obj (LocallyDiscrete.mk X)

/-- The 1-morphism assigned to an ordinary morphism. -/
abbrev pseudofunctorMap (F : PseudofunctorFromCategory A C)
    {X Y : A} (f : X ⟶ Y) : pseudofunctorObject F X ⟶ pseudofunctorObject F Y :=
  F.map (Quiver.Hom.toLoc f)

/-- The unit comparison in the direction used by the source. -/
def pseudofunctorUnitIso (F : PseudofunctorFromCategory A C) (X : A) :
    𝟙 (pseudofunctorObject F X) ≅
      pseudofunctorMap F (𝟙 X) :=
  (F.mapId (LocallyDiscrete.mk X)).symm

/-- The composition comparison in the direction used by the source. -/
def pseudofunctorCompositionIso (F : PseudofunctorFromCategory A C)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pseudofunctorMap F (f ≫ g) ≅ pseudofunctorMap F f ≫ pseudofunctorMap F g :=
  F.mapComp (Quiver.Hom.toLoc f) (Quiver.Hom.toLoc g)

/-- The unit comparison as a 2-morphism. -/
abbrev pseudofunctorUnit (F : PseudofunctorFromCategory A C) (X : A) :
    𝟙 (pseudofunctorObject F X) ⟶ pseudofunctorMap F (𝟙 X) :=
  (pseudofunctorUnitIso F X).hom

/-- The composition comparison as a 2-morphism. -/
abbrev pseudofunctorComposition (F : PseudofunctorFromCategory A C)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pseudofunctorMap F (f ≫ g) ⟶ pseudofunctorMap F f ≫ pseudofunctorMap F g :=
  (pseudofunctorCompositionIso F f g).hom

theorem pseudofunctorUnit_is_iso (F : PseudofunctorFromCategory A C) (X : A) :
    IsIso (pseudofunctorUnit F X) := by
  infer_instance

theorem pseudofunctorComposition_is_iso (F : PseudofunctorFromCategory A C)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (pseudofunctorComposition F f g) := by
  infer_instance

/- The source writes these equations after identifying composites with the
   equal 1-morphisms supplied by the ordinary category laws.  `HEq` records
   precisely that source convention while retaining the dependent types of
   Mathlib's bicategory API. -/
theorem pseudofunctor_left_unit (F : PseudofunctorFromCategory A C)
    [Bicategory.Strict C] {X Y : A} (f : X ⟶ Y) :
    HEq (pseudofunctorComposition F f (𝟙 Y))
      (horizontalComposition (pseudofunctorUnit F Y)
        (𝟙 (pseudofunctorMap F f))) := by
  simp [pseudofunctorComposition, pseudofunctorUnit,
    pseudofunctorCompositionIso, pseudofunctorUnitIso, horizontalComposition]
  rw [F.mapComp_id_right_hom (Quiver.Hom.toLoc f)]
  simp [Bicategory.Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
  exact eqToHom_comp_heq (F.map f.toLoc ◁ (F.mapId { as := Y }).inv) _

theorem pseudofunctor_right_unit (F : PseudofunctorFromCategory A C)
    [Bicategory.Strict C] {X Y : A} (f : X ⟶ Y) :
    HEq (pseudofunctorComposition F (𝟙 X) f)
      (horizontalComposition (𝟙 (pseudofunctorMap F f))
        (pseudofunctorUnit F X)) := by
  simp [pseudofunctorComposition, pseudofunctorUnit,
    pseudofunctorCompositionIso, pseudofunctorUnitIso, horizontalComposition]
  rw [F.mapComp_id_left_hom (Quiver.Hom.toLoc f)]
  simp [Bicategory.Strict.leftUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
  exact eqToHom_comp_heq ((F.mapId { as := X }).inv ▷ F.map f.toLoc) _

theorem pseudofunctor_associativity (F : PseudofunctorFromCategory A C)
    [Bicategory.Strict C] {W X Y Z : A}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    HEq
      (pseudofunctorComposition F (f ≫ g) h ≫
        horizontalComposition (𝟙 (pseudofunctorMap F h))
          (pseudofunctorComposition F f g))
      (pseudofunctorComposition F f (g ≫ h) ≫
        horizontalComposition (pseudofunctorComposition F g h)
          (𝟙 (pseudofunctorMap F f))) := by
  simp [pseudofunctorComposition, pseudofunctorCompositionIso,
    horizontalComposition]
  change
    (F.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
        (F.mapComp f.toLoc g.toLoc).hom ▷ F.map h.toLoc ≍
      (F.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).hom ≫
        F.map f.toLoc ◁ (F.mapComp g.toLoc h.toLoc).hom
  rw [F.mapComp_assoc_left_hom (Quiver.Hom.toLoc f)
    (Quiver.Hom.toLoc g) (Quiver.Hom.toLoc h)]
  simp [Bicategory.Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom]
  simpa only [Category.assoc] using
    (comp_eqToHom_heq
      ((F.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).hom ≫
        F.map f.toLoc ◁ (F.mapComp g.toLoc h.toLoc).hom)
      (Bicategory.Strict.assoc (F.map f.toLoc) (F.map g.toLoc)
        (F.map h.toLoc)).symm)

/- The source also mentions a theorem that every pseudofunctor is isomorphic
   to a functor.  It does not specify the morphisms of pseudofunctors, the
   target of the isomorphism, or the hypotheses under which strictification
   is intended, so no theorem interface is asserted here. -/

end PseudofunctorsFromCategories

end Formalization.Books.Categories.Unit29
