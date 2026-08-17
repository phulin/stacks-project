import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Widesubcategory

namespace CategoryTheory.Functor

/-- The two lifting conditions in the source definition of a category fibred
in groupoids. -/
class IsFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) : Prop where
  exists_lift : ∀ {V U : C} (f : V ⟶ U) {x : S}, p.obj x = U →
    ∃ (y : S) (φ : y ⟶ x), p.IsHomLift f φ
  unique_lift : ∀ {x y z : S} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : p.obj z ⟶ p.obj y}, f ≫ p.map φ = p.map ψ →
    ∃! χ : z ⟶ y, p.IsHomLift f χ ∧ χ ≫ φ = ψ

end CategoryTheory.Functor

/-!
# Categories, Chapter 35: Categories fibred in groupoids

The source defines a category fibred in groupoids directly by its lifting
properties, and then compares that definition with Mathlib's `IsFibered`
and `Functor.Fiber`.  The declarations below retain that source-facing
predicate while reusing the canonical Mathlib and earlier-chapter APIs for
fibres, cartesian arrows, categories over a fixed base, inertia, and
2-fibre products.
-/

namespace Formalization.Books.Categories.Unit35

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit34

universe v u v' u' u₁ v₁

noncomputable section

/-! ## The lifting definition -/

theorem fibredInGroupoids_exists_lift
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {V : C} {x : S} (f : V ⟶ p.obj x) :
    ∃ (y : S) (φ : y ⟶ x), p.IsHomLift f φ := by
  exact Functor.IsFibredInGroupoids.exists_lift f rfl

theorem fibredInGroupoids_unique_lift
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {x y z : S} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : p.obj z ⟶ p.obj y} (h : f ≫ p.map φ = p.map ψ) :
    ∃! χ : z ⟶ y, p.IsHomLift f χ ∧ χ ≫ φ = ψ := by
  exact Functor.IsFibredInGroupoids.unique_lift φ ψ h

/-- The comparison isomorphism between a chosen lift of `g ≫ f` and the
two-step lift through chosen lifts of `f` and `g`. -/
theorem fibredInGroupoids_composite_lift_isomorphic
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids]
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
    {x y z z' : S} (φ : y ⟶ x) (ψ : z ⟶ y) (γ : z' ⟶ x)
    (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ)
    (hγ : p.IsHomLift (g ≫ f) γ) :
    ∃ e : z ≅ z',
      p.IsHomLift (𝟙 (p.obj z)) e.hom ∧
        p.IsHomLift (𝟙 (p.obj z')) e.inv ∧
        e.hom ≫ γ = ψ ≫ φ ∧ e.inv ≫ (ψ ≫ φ) = γ := by
  let _ : p.IsHomLift f φ := hφ
  let _ : p.IsHomLift g ψ := hψ
  let _ : p.IsHomLift (g ≫ f) γ := hγ
  have hδ : p.IsHomLift (g ≫ f) (ψ ≫ φ) := inferInstance
  have hz : p.obj z = p.obj z' :=
    (CategoryTheory.IsHomLift.domain_eq p g ψ).trans
      (CategoryTheory.IsHomLift.domain_eq p (g ≫ f) γ).symm
  have hEq : eqToHom hz.symm ≫ p.map (ψ ≫ φ) = p.map γ := by
    rw [CategoryTheory.IsHomLift.fac' p (g ≫ f) (ψ ≫ φ),
      CategoryTheory.IsHomLift.fac' p (g ≫ f) γ]
    simp
  obtain ⟨χ, hχ, hχunique⟩ := fibredInGroupoids_unique_lift p (ψ ≫ φ) γ hEq
  rcases hχ with ⟨hχlift, hχcomp⟩
  have hEq' : eqToHom hz ≫ p.map γ = p.map (ψ ≫ φ) := by
    rw [CategoryTheory.IsHomLift.fac' p (g ≫ f) γ,
      CategoryTheory.IsHomLift.fac' p (g ≫ f) (ψ ≫ φ)]
    simp
  obtain ⟨η, hη, hηunique⟩ := fibredInGroupoids_unique_lift p γ (ψ ≫ φ) hEq'
  rcases hη with ⟨hηlift, hηcomp⟩
  have hηχ : η ≫ χ = 𝟙 z := by
    apply
      (fibredInGroupoids_unique_lift p (ψ ≫ φ) (ψ ≫ φ)
        (f := 𝟙 (p.obj z)) (by simp)).unique
    · have hcomp :
          p.IsHomLift (eqToHom hz ≫ eqToHom hz.symm) (η ≫ χ) := inferInstance
      have hcomp' : p.IsHomLift (𝟙 (p.obj z)) (η ≫ χ) := by
        simpa using hcomp
      exact ⟨hcomp', by simp [Category.assoc, hχcomp, hηcomp]⟩
    · exact ⟨inferInstance, by simp⟩
  have hχη : χ ≫ η = 𝟙 z' := by
    apply
      (fibredInGroupoids_unique_lift p γ γ
        (f := 𝟙 (p.obj z')) (by simp)).unique
    · have hcomp :
          p.IsHomLift (eqToHom hz.symm ≫ eqToHom hz) (χ ≫ η) := inferInstance
      have hcomp' : p.IsHomLift (𝟙 (p.obj z')) (χ ≫ η) := by
        simpa using hcomp
      exact ⟨hcomp', by simp [Category.assoc, hηcomp, hχcomp]⟩
    · exact ⟨inferInstance, by simp⟩
  have hηlift' : p.IsHomLift (𝟙 (p.obj z)) η := by
    apply CategoryTheory.IsHomLift.of_fac' p (𝟙 (p.obj z)) η rfl hz.symm
    rw [← CategoryTheory.IsHomLift.eq_of_isHomLift p (eqToHom hz) η]
    simp
  have hχlift' : p.IsHomLift (𝟙 (p.obj z')) χ := by
    apply CategoryTheory.IsHomLift.of_fac' p (𝟙 (p.obj z')) χ rfl hz
    rw [← CategoryTheory.IsHomLift.eq_of_isHomLift p (eqToHom hz.symm) χ]
    simp
  refine ⟨{ hom := η, inv := χ, hom_inv_id := hηχ, inv_hom_id := hχη },
    hηlift', hχlift', hηcomp, hχcomp⟩

/-! ## Equivalence with fibred categories with groupoid fibres -/

theorem fibredInGroupoids_iff_fibred_groupoid_fibres
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    p.IsFibredInGroupoids ↔
      (∀ U : C, IsGroupoid (Functor.Fiber p U)) ∧ p.IsFibered := by
  constructor
  · intro hp
    let _ : p.IsFibredInGroupoids := hp
    constructor
    · intro U
      constructor
      intro X Y f
      let _ : p.IsHomLift (𝟙 U) f.1 := f.2
      let _ : IsIso (p.map f.1) := by
        rw [CategoryTheory.IsHomLift.fac' p (𝟙 U) f.1]
        infer_instance
      let _ : Functor.IsStronglyCartesian p (p.map f.1) f.1 := by
        constructor
        intro a g τ hτ
        have hEq : g ≫ p.map f.1 = p.map τ :=
          CategoryTheory.IsHomLift.eq_of_isHomLift p (g ≫ p.map f.1) τ
        exact fibredInGroupoids_unique_lift p f.1 τ hEq
      let _ : IsIso f.1 :=
        Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map f.1) f.1
      let _ : p.IsHomLift (𝟙 U) (inv f.1) := inferInstance
      let g : Y ⟶ X := ⟨inv f.1, inferInstance⟩
      refine ⟨⟨g, ?_, ?_⟩⟩
      · apply Functor.Fiber.hom_ext
        change f.1 ≫ inv f.1 = 𝟙 X.1
        simp
      · apply Functor.Fiber.hom_ext
        change inv f.1 ≫ f.1 = 𝟙 Y.1
        simp
    · apply Functor.IsFibered.of_exists_isStronglyCartesian
      intro x R f
      obtain ⟨y, φ, hφ⟩ := hp.exists_lift f rfl
      let _ : p.IsHomLift f φ := hφ
      exact ⟨y, φ, by
        constructor
        intro a g τ hτ
        let g' := g ≫ eqToHom
          (CategoryTheory.IsHomLift.domain_eq p f φ).symm
        have htransport :
            eqToHom (CategoryTheory.IsHomLift.domain_eq p f φ).symm ≫ p.map φ =
              f ≫ eqToHom (CategoryTheory.IsHomLift.codomain_eq p f φ).symm := by
          rw [CategoryTheory.IsHomLift.fac' p f φ]
          simp
        have hmapτ : g ≫ f = p.map τ :=
          CategoryTheory.IsHomLift.eq_of_isHomLift p (g ≫ f) τ
        have hEq : g' ≫ p.map φ = p.map τ := by
          dsimp [g']
          calc
            (g ≫ eqToHom (CategoryTheory.IsHomLift.domain_eq p f φ).symm) ≫ p.map φ =
                g ≫ (eqToHom (CategoryTheory.IsHomLift.domain_eq p f φ).symm ≫
                  p.map φ) := by simp [Category.assoc]
            _ = g ≫ (f ≫ eqToHom
                (CategoryTheory.IsHomLift.codomain_eq p f φ).symm) := by
              rw [htransport]
            _ = (g ≫ f) ≫ eqToHom
                (CategoryTheory.IsHomLift.codomain_eq p f φ).symm := by
              simp
            _ = p.map τ ≫ eqToHom
                (CategoryTheory.IsHomLift.codomain_eq p f φ).symm := by
              rw [hmapτ]
            _ = p.map τ := by simp
        obtain ⟨χ, hχ, hχunique⟩ :=
          fibredInGroupoids_unique_lift p φ τ hEq
        rcases hχ with ⟨hχlift, hχcomp⟩
        let _ : p.IsHomLift g' χ := hχlift
        have hχlift' : p.IsHomLift g χ := by
          apply CategoryTheory.IsHomLift.of_commsq p g χ rfl
            (CategoryTheory.IsHomLift.domain_eq p f φ)
          rw [← CategoryTheory.IsHomLift.eq_of_isHomLift p g' χ]
          dsimp [g']
          simp [Category.assoc]
        refine ⟨χ, ⟨hχlift', hχcomp⟩, ?_⟩
        intro χ' hχ'
        apply hχunique χ'
        rcases hχ' with ⟨hχ'lift, hχ'comp⟩
        let _ : p.IsHomLift g χ' := hχ'lift
        have hmapχ' : g' = p.map χ' := by
          dsimp [g']
          rw [CategoryTheory.IsHomLift.fac p g χ']
          simp [Category.assoc]
        refine ⟨?_, hχ'comp⟩
        apply CategoryTheory.IsHomLift.of_fac' p g' χ' rfl rfl
        simpa using hmapχ'.symm⟩
  · rintro ⟨hgroup, hfib⟩
    let _ : p.IsFibered := hfib
    constructor
    · intro V U f x hx
      let f' := f ≫ eqToHom hx.symm
      obtain ⟨y, φ, hφ⟩ := hfib.toIsPreFibered.exists_isCartesian' f'
      let _ : p.IsCartesian f' φ := hφ
      refine ⟨y, φ, ?_⟩
      apply CategoryTheory.IsHomLift.of_fac' p f φ
        (CategoryTheory.IsHomLift.domain_eq p f' φ) hx
      simpa [f'] using CategoryTheory.IsHomLift.fac' p f' φ
    · intro x y z φ ψ f hcomp
      obtain ⟨y', e, he⟩ :=
        Functor.IsPreFibered.exists_isCartesian' (p := p) (p.map φ)
      let _ : p.IsCartesian (p.map φ) e := he
      let _ : Functor.IsStronglyCartesian p (p.map φ) e := inferInstance
      obtain ⟨i, ⟨hi, hie⟩, hiunique⟩ :=
        Functor.IsCartesian.universal_property (p := p) (f := p.map φ) (φ := e) φ
      let _ : p.IsHomLift (𝟙 (p.obj y)) i := hi
      obtain ⟨j, ⟨hj, hje⟩, hjunique⟩ :=
        Functor.IsStronglyCartesian.universal_property p (p.map φ) e f
          (p.map ψ) hcomp.symm ψ
      let _ : p.IsHomLift f j := hj
      let _ : IsGroupoid (Functor.Fiber p (p.obj y)) := hgroup (p.obj y)
      let _ : IsIso (Functor.Fiber.homMk p (p.obj y) i) :=
        (hgroup (p.obj y)).all_isIso _
      let iInvFiber := inv (Functor.Fiber.homMk p (p.obj y) i)
      let iInv : y' ⟶ y := Functor.Fiber.fiberInclusion.map iInvFiber
      have hiInv : p.IsHomLift (𝟙 (p.obj y)) iInv := by
        change p.IsHomLift (𝟙 (p.obj y))
          (Functor.Fiber.fiberInclusion.map iInvFiber)
        exact iInvFiber.2
      let _ : p.IsHomLift (𝟙 (p.obj y)) iInv := hiInv
      have hiiInv : i ≫ iInv = 𝟙 y := by
        have h := congrArg (fun k => k.1)
          (IsIso.hom_inv_id (Functor.Fiber.homMk p (p.obj y) i))
        change i ≫ iInvFiber.1 = 𝟙 y at h
        change i ≫ iInvFiber.1 = 𝟙 y
        exact h
      have hiInv_i : iInv ≫ i = 𝟙 y' := by
        have h := congrArg (fun k => k.1)
          (IsIso.inv_hom_id (Functor.Fiber.homMk p (p.obj y) i))
        change iInvFiber.1 ≫ i = 𝟙 y' at h
        change iInvFiber.1 ≫ i = 𝟙 y'
        exact h
      have hiInvφ : iInv ≫ φ = e := by
        rw [← hie]
        rw [← Category.assoc, hiInv_i]
        simp
      let χ : z ⟶ y := j ≫ iInv
      have hχlift : p.IsHomLift f χ := by
        have h := (inferInstance : p.IsHomLift (f ≫ 𝟙 (p.obj y)) (j ≫ iInv))
        simpa using h
      have hχcomp : χ ≫ φ = ψ := by
        dsimp [χ]
        rw [Category.assoc, hiInvφ]
        exact hje
      refine ⟨χ, ⟨hχlift, hχcomp⟩, ?_⟩
      intro χ' hχ'
      rcases hχ' with ⟨hχ'lift, hχ'comp⟩
      let _ : p.IsHomLift f χ' := hχ'lift
      have hχ'i_lift : p.IsHomLift f (χ' ≫ i) := by
        have h := (inferInstance : p.IsHomLift (f ≫ 𝟙 (p.obj y)) (χ' ≫ i))
        simpa using h
      let _ : p.IsHomLift f (χ' ≫ i) := hχ'i_lift
      have hχ'i : χ' ≫ i = j := by
        apply Functor.IsStronglyCartesian.ext p (p.map φ) e f
        calc
          (χ' ≫ i) ≫ e = χ' ≫ (i ≫ e) := by simp [Category.assoc]
          _ = χ' ≫ φ := by rw [hie]
          _ = ψ := hχ'comp
          _ = j ≫ e := hje.symm
      calc
        χ' = χ' ≫ 𝟙 y := by simp
        _ = χ' ≫ (i ≫ iInv) := by rw [hiiInv]
        _ = (χ' ≫ i) ≫ iInv := by simp [Category.assoc]
        _ = j ≫ iInv := by rw [hχ'i]
        _ = χ := rfl

theorem fibredInGroupoids_all_morphisms_stronglyCartesian
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) (hp : p.IsFibredInGroupoids)
    {x y : S} (φ : x ⟶ y) :
    Functor.IsStronglyCartesian p (p.map φ) φ := by
  constructor
  intro a g τ hτ
  have hEq : g ≫ p.map φ = p.map τ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift p (g ≫ p.map φ) τ
  exact hp.unique_lift φ τ hEq

/- The chosen-pullback construction from Unit 33 is the source's
`f^* x → x` data.  The additional field records that the Cat-valued
pseudofunctor has groupoid values; the bridge theorem below exposes this
property on its actual `Pith` objects without duplicating the Unit 33 API. -/
structure FibredInGroupoidsPseudofunctorData
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  data : PullbackPseudofunctorData p P
  fibre_is_groupoid : ∀ U : C, IsGroupoid (Functor.Fiber p U)

theorem fibredInGroupoids_pseudofunctor_object_is_groupoid
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (D : FibredInGroupoidsPseudofunctorData p P) (U : C) :
    IsGroupoid (pseudofunctorObject D.data.value (Opposite.op U)).as := by
  rw [D.data.object_fibre U]
  exact D.fibre_is_groupoid U

theorem fibredInGroupoids_pseudofunctor_exists
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered]
    (hp : p.IsFibredInGroupoids) (P : PullbackChoice p) :
    Nonempty (FibredInGroupoidsPseudofunctorData p P) := by
  obtain ⟨D⟩ := pullback_pseudofunctor_exists p P
  exact ⟨{
    data := D
    fibre_is_groupoid :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.1
  }⟩

/-! ## The strongly-cartesian wide subcategory -/

def stronglyCartesianMorphismProperty
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : MorphismProperty S :=
  fun {_x _y} φ => Functor.IsStronglyCartesian p (p.map φ) φ

instance stronglyCartesianMorphismProperty_isMultiplicative
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    (stronglyCartesianMorphismProperty p).IsMultiplicative where
  id_mem := by
    intro x
    change Functor.IsStronglyCartesian p (p.map (𝟙 x)) (𝟙 x)
    infer_instance
  comp_mem := by
    intro x y z f g hf hg
    change Functor.IsStronglyCartesian p (p.map (f ≫ g)) (f ≫ g)
    rw [p.map_comp]
    exact @Functor.IsStronglyCartesian.comp _ _ _ _ p
      (p.obj x) (p.obj y) (p.obj z) x y z (p.map f) (p.map g) f g hf hg

abbrev StronglyCartesianSubcategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :=
  WideSubcategory (stronglyCartesianMorphismProperty p)

def stronglyCartesianSubcategoryInclusion
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    StronglyCartesianSubcategory p ⥤ S :=
  wideSubcategoryInclusion (stronglyCartesianMorphismProperty p)

def stronglyCartesianSubcategoryProjection
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    StronglyCartesianSubcategory p ⥤ C :=
  stronglyCartesianSubcategoryInclusion p ⋙ p

theorem stronglyCartesianSubcategory_hom_property
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered]
    {x y : StronglyCartesianSubcategory p} (φ : x ⟶ y) :
    Functor.IsStronglyCartesian p (p.map φ.hom) φ.hom :=
  φ.property

theorem stronglyCartesianSubcategory_isFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    (stronglyCartesianSubcategoryProjection p).IsFibredInGroupoids := by
  constructor
  · intro V U f x hx
    change p.obj x.obj = U at hx
    subst U
    obtain ⟨y, φ, hφ⟩ :=
      (fibred_category_iff_exists_stronglyCartesian p).mp (inferInstance)
        x.obj V f
    let _ : p.IsStronglyCartesian f φ := hφ
    have hdom : p.obj y = V :=
      CategoryTheory.IsHomLift.domain_eq p f φ
    have hmap : f = p.map φ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p f φ
    have hφ' : p.IsStronglyCartesian (p.map φ) φ := by
      simpa [hmap] using (inferInstance : p.IsStronglyCartesian f φ)
    refine ⟨⟨y, hdom⟩, ⟨φ, hφ'⟩, ?_⟩
    change p.IsHomLift f φ
    infer_instance
  · intro x y z φ ψ f hcomp
    change f ≫ p.map φ.hom = p.map ψ.hom at hcomp
    let _ : p.IsStronglyCartesian (p.map φ.hom) φ.hom :=
      stronglyCartesianSubcategory_hom_property p φ
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p (p.map φ.hom) φ.hom
        f (p.map ψ.hom) hcomp.symm ψ.hom
    let _ : p.IsHomLift f χ := hχ
    have hcompStrong :
        p.IsStronglyCartesian (p.map (χ ≫ φ.hom)) (χ ≫ φ.hom) := by
      simpa [hχfac] using stronglyCartesianSubcategory_hom_property p ψ
    have hcompStrong' :
        p.IsStronglyCartesian (p.map χ ≫ p.map φ.hom) (χ ≫ φ.hom) := by
      simpa using hcompStrong
    let _ : p.IsStronglyCartesian
        (p.map χ ≫ p.map φ.hom) (χ ≫ φ.hom) := hcompStrong'
    have hχstrong : p.IsStronglyCartesian (p.map χ) χ := by
      exact Functor.IsStronglyCartesian.of_comp p
    refine ⟨⟨χ, hχstrong⟩, ?_, ?_⟩
    · change p.IsHomLift f χ
      exact hχ
    · change χ ≫ φ.hom = ψ.hom
      exact hχfac
    · intro χ' hχ'
      apply WideSubcategory.hom_ext
      apply hχuniq χ'.hom
      rcases hχ' with ⟨hχ', hχ'fac⟩
      constructor
      · change p.IsHomLift f χ'.hom
        exact hχ'
      · change χ'.hom ≫ φ.hom = ψ.hom
        exact hχ'fac

/-! ## Examples -/

theorem groupHomomorphism_fibredInGroupoids_iff_surjective
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    (MonoidHom.toFunctor p).IsFibredInGroupoids ↔ Function.Surjective p := by
  constructor
  · intro hp b
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift
      (V := SingleObj.star H) (U := SingleObj.star H) b
      (x := SingleObj.star G) rfl
    change p φ = b
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidHom.toFunctor p) b φ).symm
  · intro hs
    constructor
    · intro V U f x hx
      obtain ⟨g, hg⟩ := hs f
      refine ⟨SingleObj.star G, g, ?_⟩
      change p g = f
      exact hg
    · intro x y z φ ψ f hcomp
      change p φ * f = p ψ at hcomp
      have hχ : f = p ((φ : G)⁻¹ * (ψ : G)) := by
        change f = p ((φ : G)⁻¹ * (ψ : G))
        rw [map_mul, ← hcomp]
        simp [mul_assoc]
      refine ⟨(φ : G)⁻¹ * (ψ : G), ?_, ?_⟩
      · constructor
        · rw [hχ]
          infer_instance
        · change (φ : G) * ((φ : G)⁻¹ * (ψ : G)) = (ψ : G)
          simp [mul_assoc]
      · intro χ hχ'
        rcases hχ' with ⟨_, hχ'⟩
        change (χ : G) = (φ : G)⁻¹ * (ψ : G)
        change (φ : G) * (χ : G) = (ψ : G) at hχ'
        rw [← hχ']
        simp [mul_assoc]

theorem groupHomomorphism_fibre_is_kernel_groupoid
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    Nonempty
      (Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ≌
        SingleObj (MonoidHom.ker p)) := by
  have fiber_hom_mem : ∀ {x y : Functor.Fiber (MonoidHom.toFunctor p)
      (SingleObj.star H)} (f : x ⟶ y), p f.1 = 1 := by
    intro x y f
    let _ : (MonoidHom.toFunctor p).IsHomLift
        (𝟙 (SingleObj.star H)) f.1 := f.2
    have hf := CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidHom.toFunctor p) (𝟙 (SingleObj.star H)) f.1
    simpa [SingleObj.id_as_one] using hf.symm
  let F : Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ⥤
      SingleObj (MonoidHom.ker p) where
    obj _ := SingleObj.star (MonoidHom.ker p)
    map f := ⟨f.1, fiber_hom_mem f⟩
    map_id := by
      intro x
      apply Subtype.ext
      rfl
    map_comp := by
      intro x y z f g
      apply Subtype.ext
      rfl
  let G : SingleObj (MonoidHom.ker p) ⥤
      Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) where
    obj _ := ⟨SingleObj.star G, rfl⟩
    map f := ⟨f.1, by
      have hf : (𝟙 (SingleObj.star H)) = p f.1 := by
        simpa [SingleObj.id_as_one] using f.2.symm
      rw [hf]
      infer_instance⟩
    map_id := by
      intro x
      apply Functor.Fiber.hom_ext
      rfl
    map_comp := by
      intro x y z f g
      apply Functor.Fiber.hom_ext
      rfl
  refine ⟨{ functor := F, inverse := G, unitIso := ?_, counitIso := ?_ }⟩
  · refine NatIso.ofComponents
      (fun x => eqToIso (Subsingleton.elim x (G.obj (F.obj x)))) ?_
    intro x y f
    apply Functor.Fiber.hom_ext
    simp
  · refine NatIso.ofComponents (fun x => Iso.refl _) ?_
    intro x y f
    rfl

/-- The base category in the finite counterexample has the chain
`A → B → T`, with the composite as its unique arrow `A → T`. -/
inductive FiniteExampleBase
  | A | B | T
  deriving DecidableEq

def finiteExampleBaseLE : FiniteExampleBase → FiniteExampleBase → Prop
  | .A, .A | .B, .B | .T, .T | .A, .B | .B, .T | .A, .T => True
  | _, _ => False

instance finiteExampleBasePartialOrder : PartialOrder FiniteExampleBase where
  le := finiteExampleBaseLE
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro x y z hxy hyz
    change finiteExampleBaseLE x y at hxy
    change finiteExampleBaseLE y z at hyz
    cases x <;> cases y <;> cases z <;> simp_all [finiteExampleBaseLE]
  le_antisymm := by
    intro x y hxy hyx
    change finiteExampleBaseLE x y at hxy
    change finiteExampleBaseLE y x at hyx
    cases x <;> cases y <;> simp_all [finiteExampleBaseLE]

inductive FiniteExampleSource
  | A | B | T
  deriving DecidableEq

def finiteExampleSourceLE : FiniteExampleSource → FiniteExampleSource → Prop
  | .A, .A | .B, .B | .T, .T | .A, .T | .B, .T => True
  | _, _ => False

instance finiteExampleSourcePartialOrder : PartialOrder FiniteExampleSource where
  le := finiteExampleSourceLE
  le_refl := by
    intro x
    cases x <;> trivial
  le_trans := by
    intro x y z hxy hyz
    change finiteExampleSourceLE x y at hxy
    change finiteExampleSourceLE y z at hyz
    cases x <;> cases y <;> cases z <;> simp_all [finiteExampleSourceLE]
  le_antisymm := by
    intro x y hxy hyx
    change finiteExampleSourceLE x y at hxy
    change finiteExampleSourceLE y x at hyx
    cases x <;> cases y <;> simp_all [finiteExampleSourceLE]

def finiteExampleSourceToBase : FiniteExampleSource → FiniteExampleBase
  | .A => .A
  | .B => .B
  | .T => .T

theorem finiteExample_source_le_implies_base_le
    {x y : FiniteExampleSource} (h : x ≤ y) :
    finiteExampleSourceToBase x ≤ finiteExampleSourceToBase y := by
  change finiteExampleSourceLE x y at h
  change finiteExampleBaseLE (finiteExampleSourceToBase x)
    (finiteExampleSourceToBase y)
  cases x <;> cases y <;> simp_all [finiteExampleSourceLE, finiteExampleBaseLE,
    finiteExampleSourceToBase]

def finiteExampleFunctor : FiniteExampleSource ⥤ FiniteExampleBase where
  obj := finiteExampleSourceToBase
  map f := homOfLE (finiteExample_source_le_implies_base_le f.le)
  map_id := by
    intro x
    apply Subsingleton.elim
  map_comp := by
    intro x y z f g
    apply Subsingleton.elim

def finiteExampleBaseF : FiniteExampleBase.A ⟶ FiniteExampleBase.B :=
  homOfLE (by
    change finiteExampleBaseLE .A .B
    trivial)

theorem finiteExample_fibre_categories_are_groupoids :
    ∀ U : FiniteExampleBase,
      IsGroupoid (Functor.Fiber finiteExampleFunctor U) := by
  intro U
  constructor
  intro X Y f
  have hXY : X = Y := by
    apply Subtype.ext
    rcases X with ⟨x, hx⟩
    rcases Y with ⟨y, hy⟩
    change finiteExampleSourceToBase x = U at hx
    change finiteExampleSourceToBase y = U at hy
    cases x <;> cases y <;> cases hx <;> cases hy <;> rfl
  subst hXY
  have hf : f = 𝟙 X := by
    apply Functor.Fiber.hom_ext
    change (f.1 : X.1 ⟶ X.1) = 𝟙 _
    apply Subsingleton.elim
  rw [hf]
  infer_instance

theorem finiteExample_no_lift_of_f :
    ¬ ∃ (y : FiniteExampleSource) (φ : y ⟶ FiniteExampleSource.B),
      finiteExampleFunctor.IsHomLift finiteExampleBaseF φ := by
  rintro ⟨y, φ, hφ⟩
  have hle : y ≤ FiniteExampleSource.B := φ.le
  change finiteExampleSourceLE y FiniteExampleSource.B at hle
  cases y
  · simp [finiteExampleSourceLE] at hle
  · have hy := CategoryTheory.IsHomLift.domain_eq finiteExampleFunctor finiteExampleBaseF φ
    simp [finiteExampleFunctor, finiteExampleSourceToBase] at hy
  · simp [finiteExampleSourceLE] at hle

theorem finiteExample_not_fibredInGroupoids :
    ¬ finiteExampleFunctor.IsFibredInGroupoids := by
  intro hp
  apply finiteExample_no_lift_of_f
  exact hp.exists_lift finiteExampleBaseF rfl

/-- The second finite example is detected when distinct lifts become equal
after a common postcomposition. -/
theorem two_distinct_lifts_with_equal_postcomposition_not_fibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) {x y z : S} (f : p.obj x ⟶ p.obj y)
    (φ ψ : x ⟶ y) (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift f ψ)
    (k : y ⟶ z) (hcomp : φ ≫ k = ψ ≫ k)
    (hne : φ ≠ ψ) :
    ¬ p.IsFibredInGroupoids := by
  intro hp
  letI : p.IsHomLift f φ := hφ
  letI : p.IsHomLift f ψ := hψ
  letI : Functor.IsStronglyCartesian p (p.map k) k :=
    fibredInGroupoids_all_morphisms_stronglyCartesian p hp k
  apply hne
  exact Functor.IsStronglyCartesian.ext p (p.map k) k f hcomp

/-! ## The fixed-base 2-category -/

/-- The groupoid-fibre object property on the fixed-base fibred-category
interface from Unit 33. -/
def IsGroupoidFibredCategoryOver {C : Cat.{v, u}}
    (X : FibredCategoryOver C) : Prop :=
  ∀ U : C, IsGroupoid (Functor.Fiber (structureFunctor X.underlying) U)

theorem groupoidFibredCategoryOver_isFibredInGroupoids
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X) :
    (structureFunctor X.underlying).IsFibredInGroupoids := by
  exact (fibredInGroupoids_iff_fibred_groupoid_fibres
    (structureFunctor X.underlying)).mpr ⟨hX, inferInstance⟩

def groupoidFibredObjectProperty {C : Cat.{v, u}} :
    ObjectProperty (FibredCategoryOver C) :=
  IsGroupoidFibredCategoryOver

/- A source 1-morphism only asks for a functor over `C`.  Unit 33 packages
   such morphisms with a preservation proof, which is automatic when the
   target has groupoid fibres because every target morphism is strongly
   cartesian. -/
theorem mapsStronglyCartesian_to_groupoidFibred
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    MapsStronglyCartesian
      (structureFunctor X.underlying) (structureFunctor Y.underlying)
      (overFunctor F) := by
  intro a b φ _hφ
  exact fibredInGroupoids_all_morphisms_stronglyCartesian
    (structureFunctor Y.underlying)
    (groupoidFibredCategoryOver_isFibredInGroupoids Y hY)
    ((overFunctor F).map φ)

def fibredCategoryOverHomOfGroupoid
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : CategoryOverHom X.underlying Y.underlying) :
    FibredCategoryOverHom X Y where
  underlying := F
  preserves := mapsStronglyCartesian_to_groupoidFibred hY F

/-- The source's 2-category of categories fibred in groupoids over `C`.
It is the full sub-2-category on the groupoid-fibre objects. -/
abbrev CategoriesFibredInGroupoidsOver (C : Cat.{v, u}) :=
  FullSubTwoCategory (FibredCategoryOver C) (groupoidFibredObjectProperty (C := C))

theorem fibredInGroupoids_two_morphism_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    {F G : FibredCategoryOverHom X Y} (η : F ⟶ G) : IsIso η := by
  have hη : IsIso η.toNatTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    let U := (structureFunctor X.underlying).obj Z
    let z : Functor.Fiber (structureFunctor X.underlying) U := ⟨Z, rfl⟩
    letI : IsGroupoid (Functor.Fiber (structureFunctor Y.underlying) U) := hY U
    change IsIso (Functor.Fiber.fiberInclusion.map
      ((overMorphismFiberNatTrans η U).app z))
    infer_instance
  let e : overFunctor F.underlying ≅ overFunctor G.underlying :=
    { hom := η.toNatTrans
      inv := inv η.toNatTrans
      hom_inv_id := by simp
      inv_hom_id := by simp }
  let E : F.underlying ≅ G.underlying :=
    overNatIsoOfUnderlying e (by
      intro Z
      exact η.over Z)
  let E' : F ≅ G := fibredHomIsoOfUnderlying E
  have hE : E'.hom = η := by
    apply OverNatTrans.ext
    rfl
  rw [← hE]
  infer_instance

theorem categoriesFibredInGroupoidsOver_is_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory
      (CategoriesFibredInGroupoidsOver C) := by
  intro X Y
  refine ⟨fun {F G} η => ?_⟩
  letI : IsIso η.hom := fibredInGroupoids_two_morphism_isIso
    (X := X.obj) (Y := Y.obj) Y.property η.hom
  refine ⟨⟨inv η.hom⟩, ?_, ?_⟩
  · apply Bicategory.InducedBicategory.hom₂_ext
    change η.hom ≫ inv η.hom = 𝟙 F.hom
    simp
  · apply Bicategory.InducedBicategory.hom₂_ext
    change inv η.hom ≫ η.hom = 𝟙 G.hom
    simp

/-! ## 2-fibre products over a fixed base -/

structure FibredInGroupoidsTwoFibreProduct
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  product : FibredTwoFibreProduct.{u₁, v₁, v, u} F G
  fibres_are_groupoids : ∀ U : C,
    IsGroupoid (Functor.Fiber product.diagram.base U)

theorem fibredInGroupoidsTwoFibreProduct_apex_isFibredInGroupoids
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    {F : FibredCategoryOverHom X S} {G : FibredCategoryOverHom Y S}
    (P : FibredInGroupoidsTwoFibreProduct F G) :
    P.product.diagram.base.IsFibredInGroupoids := by
  exact (fibredInGroupoids_iff_fibred_groupoid_fibres
    P.product.diagram.base).mpr
    ⟨P.fibres_are_groupoids, P.product.apex_fibred⟩

theorem categoriesFibredInGroupoids_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (hS : IsGroupoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInGroupoidsTwoFibreProduct F G) := by
  obtain ⟨P⟩ := fibred_categories_have_two_fibre_products X Y S F G
  refine ⟨{ product := P, fibres_are_groupoids := ?_ }⟩
  intro U
  constructor
  intro a b f
  let D := P.diagram
  let _ : D.base.IsHomLift (𝟙 U) f.1 := f.2
  have hleft : (structureFunctor X.underlying).obj (D.left.obj a.1) = U := by
    have h := congrArg
      (fun H : TwoFibreProductOverCategory F.underlying G.underlying ⥤ C =>
        H.obj a.1) D.left_over
    exact h.trans a.2
  have hleft' : (structureFunctor X.underlying).obj (D.left.obj b.1) = U := by
    have h := congrArg
      (fun H : TwoFibreProductOverCategory F.underlying G.underlying ⥤ C =>
        H.obj b.1) D.left_over
    exact h.trans b.2
  have r := Functor.congr_obj D.right_over a.1
  have r' := Functor.congr_obj D.right_over b.1
  let hright : (structureFunctor Y.underlying).obj (D.right.obj a.1) = U :=
    r.trans a.2
  let hright' : (structureFunctor Y.underlying).obj (D.right.obj b.1) = U :=
    r'.trans b.2
  let leftMap :
      (⟨D.left.obj a.1, hleft⟩ : Functor.Fiber
        (structureFunctor X.underlying) U) ⟶
      (⟨D.left.obj b.1, hleft'⟩ : Functor.Fiber
        (structureFunctor X.underlying) U) := by
    refine ⟨D.left.map f.1, ?_⟩
    apply IsHomLift.of_fac' (structureFunctor X.underlying) (𝟙 U)
      (D.left.map f.1) hleft hleft'
    calc
      (structureFunctor X.underlying).map (D.left.map f.1) =
          (D.left ⋙ structureFunctor X.underlying).map f.1 := rfl
      _ = D.base.map f.1 := Functor.congr_hom D.left_over f.1
      _ = eqToHom a.2 ≫ 𝟙 U ≫ eqToHom b.2.symm :=
        IsHomLift.fac' D.base (𝟙 U) f.1
      _ = eqToHom hleft ≫ 𝟙 U ≫ eqToHom hleft'.symm := by
        simp [hleft, hleft', eqToHom_trans]
  let rightMap :
      (⟨D.right.obj a.1, hright⟩ : Functor.Fiber
        (structureFunctor Y.underlying) U) ⟶
      (⟨D.right.obj b.1, hright'⟩ : Functor.Fiber
        (structureFunctor Y.underlying) U) := by
    refine ⟨D.right.map f.1, ?_⟩
    apply IsHomLift.of_fac' (structureFunctor Y.underlying) (𝟙 U)
      (D.right.map f.1) hright hright'
    calc
      (structureFunctor Y.underlying).map (D.right.map f.1) =
          (D.right ⋙ structureFunctor Y.underlying).map f.1 := rfl
      _ = D.base.map f.1 := Functor.congr_hom D.right_over f.1
      _ = eqToHom a.2 ≫ 𝟙 U ≫ eqToHom b.2.symm :=
        IsHomLift.fac' D.base (𝟙 U) f.1
      _ = eqToHom hright ≫ 𝟙 U ≫ eqToHom hright'.symm := by
        simp [hright, hright', eqToHom_trans]
  let eX : D.left.obj a.1 ≅ D.left.obj b.1 :=
    (Functor.Fiber.fiberInclusion (p := structureFunctor X.underlying)
      (S := U)).mapIso (asIso leftMap)
  let eY : D.right.obj a.1 ≅ D.right.obj b.1 :=
    (Functor.Fiber.fiberInclusion (p := structureFunctor Y.underlying)
      (S := U)).mapIso (asIso rightMap)
  let e : a.1 ≅ b.1 :=
    (TwoFibreProductOverProperty F.underlying G.underlying).isoMk
      (Comma.isoMk eX eY (by
        change (overFunctor F.underlying).map (D.left.map f.1) ≫
            b.1.obj.obj.hom =
          a.1.obj.obj.hom ≫
            (overFunctor G.underlying).map (D.right.map f.1)
        exact f.1.hom.hom.w))
  have he : e.hom = f.1 := by
    apply (TwoFibreProductOverProperty F.underlying G.underlying).hom_ext
    apply Comma.hom_ext
    · rfl
    · rfl
  rw [← he]
  infer_instance

/-- The two descriptions of the category-valued 2-fibre product in the
source are canonically equivalent for categories fibred in groupoids: the
fixed-base presentation remembers a base object, while `IsoComma` remembers
only the isomorphism. -/
theorem twoFibreProductOverCategory_canonically_equivalent
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (hS : IsGroupoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty
      (TwoFibreProductOverCategory F.underlying G.underlying ≌
        IsoComma (overFunctor F.underlying) (overFunctor G.underlying)) := by
  sorry

/-! ## Fibrewise functors and equivalences -/

/-- The functor induced on fibre categories by a functor over the base. -/
def fibreFunctor
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p) (U : C) :
    Functor.Fiber p U ⥤ Functor.Fiber p' U where
  obj x :=
    ⟨G.obj x.1,
      (congrArg (fun H : S ⥤ C => H.obj x.1) over).trans x.2⟩
  map {x y} f :=
    ⟨G.map f.1, by
      let hx := (congrArg (fun H : S ⥤ C => H.obj x.1) over).trans x.2
      let hy := (congrArg (fun H : S ⥤ C => H.obj y.1) over).trans y.2
      exact IsHomLift.of_commsq p' (𝟙 U) (G.map f.1) hx hy <|
        by
          simpa [hx, hy,
            @IsHomLift.fac' _ _ _ _ p U U x.1 y.1 (𝟙 U) f.1 f.2,
            Category.assoc] using
            congrArg (fun k => k ≫ eqToHom y.2)
              ((eqToIso over).hom.naturality f.1)⟩
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    change G.map (𝟙 x.1) = 𝟙 (G.obj x.1)
    simp
  map_comp := by
    intro x y z f g
    apply Functor.Fiber.hom_ext
    change G.map (f.1 ≫ g.1) = G.map f.1 ≫ G.map g.1
    simp

theorem fibredInGroupoids_faithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    G.Faithful ↔ ∀ U : C, (fibreFunctor p p' G over U).Faithful := by
  constructor
  · intro hG U
    constructor
    intro x y f g hfg
    apply Functor.Fiber.hom_ext
    apply hG.map_injective
    exact congrArg (fun k => k.1) hfg
  · intro hG
    constructor
    intro x y f g hfg
    obtain ⟨x', φ, hφ⟩ := hp.exists_lift (p.map f) rfl
    let _ : p.IsHomLift (p.map f) φ := hφ
    let _ : p.IsStronglyCartesian (p.map φ) φ :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p hp φ
    have hdom : p.obj x' = p.obj x :=
      CategoryTheory.IsHomLift.domain_eq p (p.map f) φ
    let hx : p'.obj (G.obj x) = p.obj x :=
      congrArg (fun K : S ⥤ C => K.obj x) over
    let hy : p'.obj (G.obj y) = p.obj y :=
      congrArg (fun K : S ⥤ C => K.obj y) over
    let hx' : p'.obj (G.obj x') = p.obj x' :=
      congrArg (fun K : S ⥤ C => K.obj x') over
    have hcompf :
        eqToHom hdom.symm ≫ p.map φ = p.map f := by
      rw [CategoryTheory.IsHomLift.fac' p (p.map f) φ]
      simp
    have hbase : p.map f = p.map g := by
      have hFmap : p'.map (G.map f) =
          eqToHom hx ≫ p.map f ≫ eqToHom hy.symm := by
        exact Functor.congr_hom over f
      have hGmap : p'.map (G.map g) =
          eqToHom hx ≫ p.map g ≫ eqToHom hy.symm := by
        exact Functor.congr_hom over g
      have h' :
          eqToHom hx ≫ p.map f ≫ eqToHom hy.symm =
            eqToHom hx ≫ p.map g ≫ eqToHom hy.symm := by
        rw [← hFmap, congrArg p'.map hfg, hGmap]
      apply (cancel_epi (eqToHom hx)).1
      apply (cancel_mono (eqToHom hy.symm)).1
      simpa [Category.assoc] using h'
    obtain ⟨e, ⟨he, hef⟩, _⟩ :=
      Functor.IsStronglyCartesian.universal_property p
        (p.map φ) φ (eqToHom hdom.symm) (p.map f) hcompf f
    obtain ⟨e', ⟨he', he'g⟩, _⟩ :=
      Functor.IsStronglyCartesian.universal_property p
        (p.map φ) φ (eqToHom hdom.symm) (p.map g)
        (hcompf.trans hbase) g
    let _ : p.IsHomLift (eqToHom hdom.symm) e := he
    let _ : p.IsHomLift (eqToHom hdom.symm) e' := he'
    have hebase : p.map e = eqToHom hdom.symm := by
      simpa using
        (CategoryTheory.IsHomLift.fac' p (eqToHom hdom.symm) e)
    have he'base : p.map e' = eqToHom hdom.symm := by
      simpa using
        (CategoryTheory.IsHomLift.fac' p (eqToHom hdom.symm) e')
    let U := p.obj x'
    let eF :
        (⟨x, hdom.symm⟩ : Functor.Fiber p U) ⟶
        (⟨x', rfl⟩ : Functor.Fiber p U) := by
      refine ⟨e, ?_⟩
      apply IsHomLift.of_fac' p (𝟙 U) e hdom.symm rfl
      simpa using
        (CategoryTheory.IsHomLift.fac' p (eqToHom hdom.symm) e)
    let e'F :
        (⟨x, hdom.symm⟩ : Functor.Fiber p U) ⟶
        (⟨x', rfl⟩ : Functor.Fiber p U) := by
      refine ⟨e', ?_⟩
      apply IsHomLift.of_fac' p (𝟙 U) e' hdom.symm rfl
      simpa using
        (CategoryTheory.IsHomLift.fac' p (eqToHom hdom.symm) e')
    have hOverE : p'.map (G.map e) =
        eqToHom hx ≫ p.map e ≫ eqToHom hx'.symm := by
      exact Functor.congr_hom over e
    have hOverE' : p'.map (G.map e') =
        eqToHom hx ≫ p.map e' ≫ eqToHom hx'.symm := by
      exact Functor.congr_hom over e'
    have hGe : p'.map (G.map e) = p'.map (G.map e') := by
      rw [hOverE, hOverE', hebase, he'base]
    let _ : p'.IsHomLift (p'.map (G.map e)) (G.map e') := by
      rw [hGe]
      infer_instance
    let _ : p'.IsStronglyCartesian (p'.map (G.map φ)) (G.map φ) :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p' hp' (G.map φ)
    have hGcomp :
        G.map e ≫ G.map φ = G.map e' ≫ G.map φ := by
      calc
        G.map e ≫ G.map φ = G.map (e ≫ φ) := by simp
        _ = G.map f := congrArg G.map hef
        _ = G.map g := congrArg G.map hfg
        _ = G.map (e' ≫ φ) := congrArg G.map he'g.symm
        _ = G.map e' ≫ G.map φ := by simp
    have heG : G.map e = G.map e' :=
      Functor.IsStronglyCartesian.ext p' (p'.map (G.map φ))
        (G.map φ) (p'.map (G.map e)) hGcomp
    have heFmap :
        (fibreFunctor p p' G over U).map eF =
          (fibreFunctor p p' G over U).map e'F := by
      apply Functor.Fiber.hom_ext
      change G.map e = G.map e'
      exact heG
    have heF' : eF = e'F := (hG U).map_injective heFmap
    have he' : e = e' := congrArg (fun k => k.1) heF'
    calc
      f = e ≫ φ := hef.symm
      _ = e' ≫ φ := by rw [he']
      _ = g := he'g

theorem fibredInGroupoids_fullyFaithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    Nonempty G.FullyFaithful ↔
      ∀ U : C, Nonempty (fibreFunctor p p' G over U).FullyFaithful := by
  classical
  constructor
  · rintro ⟨hG⟩ U
    letI : G.FullyFaithful := hG
    let preimage {x y : Functor.Fiber p U}
        (h : (fibreFunctor p p' G over U).obj x ⟶
          (fibreFunctor p p' G over U).obj y) : x ⟶ y := by
      let hx₀ : p'.obj (G.obj x.1) = p.obj x.1 :=
        congrArg (fun K : S ⥤ C => K.obj x.1) over
      let hy₀ : p'.obj (G.obj y.1) = p.obj y.1 :=
        congrArg (fun K : S ⥤ C => K.obj y.1) over
      let hx : p'.obj (G.obj x.1) = U := hx₀.trans x.2
      let hy : p'.obj (G.obj y.1) = U := hy₀.trans y.2
      let _ : p'.IsHomLift (𝟙 U) h.1 := h.2
      have hfac : p'.map h.1 =
          eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm := by
        simpa [fibreFunctor, hx, hy] using
          (CategoryTheory.IsHomLift.fac' p' (𝟙 U) h.1)
      let f := G.preimage h.1
      have hOver : p'.map (G.map f) =
          eqToHom hx₀ ≫ p.map f ≫ eqToHom hy₀.symm := by
        exact Functor.congr_hom over f
      have hmap : p.map f =
          eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm := by
        apply (cancel_epi (eqToHom hx₀)).1
        apply (cancel_mono (eqToHom hy₀.symm)).1
        calc
          eqToHom hx₀ ≫ p.map f ≫ eqToHom hy₀.symm =
              p'.map (G.map f) := hOver.symm
          _ = p'.map h.1 := by
            simpa [f] using congrArg p'.map (G.map_preimage h.1)
          _ = eqToHom hx ≫ 𝟙 U ≫ eqToHom hy.symm := hfac
          _ = eqToHom hx₀ ≫
              (eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm) ≫
                eqToHom hy₀.symm := by
            simp [hx, hy, eqToHom_trans, Category.assoc]
      refine ⟨f, ?_⟩
      apply IsHomLift.of_fac' p (𝟙 U) f x.2 y.2
      exact hmap
    refine ⟨{ preimage := preimage, map_preimage := ?_, preimage_map := ?_ }⟩
    · intro x y h
      apply Functor.Fiber.hom_ext
      simpa [preimage, fibreFunctor] using hG.map_preimage h.1
    · intro x y f
      apply Functor.Fiber.hom_ext
      simpa [preimage, fibreFunctor] using hG.preimage_map f.1
  · intro hG
    have hfaith : G.Faithful := by
      apply (fibredInGroupoids_faithful_iff_fibrewise
        p p' G over hp hp').mpr
      intro U
      exact (Classical.choice (hG U)).faithful
    have exists_preimage : ∀ {x y : S} (h : G.obj x ⟶ G.obj y),
        ∃ f : x ⟶ y, G.map f = h := by
      intro x y h
      let hx₀ : p'.obj (G.obj x) = p.obj x :=
        congrArg (fun K : S ⥤ C => K.obj x) over
      let hy₀ : p'.obj (G.obj y) = p.obj y :=
        congrArg (fun K : S ⥤ C => K.obj y) over
      obtain ⟨x', φ, hφ⟩ := hp.exists_lift (p'.map h) hy₀.symm
      let _ : p.IsHomLift (p'.map h) φ := hφ
      have hdom : p.obj x' = p'.obj (G.obj x) :=
        CategoryTheory.IsHomLift.domain_eq p (p'.map h) φ
      let hx'₀ : p'.obj (G.obj x') = p.obj x' :=
        congrArg (fun K : S ⥤ C => K.obj x') over
      let hdomx : p.obj x' = p.obj x := hdom.trans hx₀
      let hx' : p'.obj (G.obj x') = p.obj x := hx'₀.trans hdomx
      have hφmap : p.map φ =
          eqToHom hdom ≫ p'.map h ≫ eqToHom hy₀ := by
        simpa using
          (CategoryTheory.IsHomLift.fac' p (p'.map h) φ)
      have hGφ : p'.map (G.map φ) =
          eqToHom hx'₀ ≫ p.map φ ≫ eqToHom hy₀.symm := by
        exact Functor.congr_hom over φ
      let gbase : p'.obj (G.obj x) ⟶ p'.obj (G.obj x') :=
        eqToHom hx₀ ≫ eqToHom hdomx.symm ≫ eqToHom hx'₀.symm
      have hcomp : gbase ≫ p'.map (G.map φ) = p'.map h := by
        rw [hGφ, hφmap]
        simp [gbase, hdomx, Category.assoc]
      let _ : p'.IsStronglyCartesian
          (p'.map (G.map φ)) (G.map φ) :=
        fibredInGroupoids_all_morphisms_stronglyCartesian p' hp' (G.map φ)
      obtain ⟨e, ⟨he, hecomp⟩, _⟩ :=
        Functor.IsStronglyCartesian.universal_property p'
          (p'.map (G.map φ)) (G.map φ) gbase (p'.map h) hcomp h
      let eF :
          (⟨G.obj x, hx₀⟩ : Functor.Fiber p' (p.obj x)) ⟶
          (⟨G.obj x', hx'⟩ : Functor.Fiber p' (p.obj x)) := by
        refine ⟨e, ?_⟩
        apply IsHomLift.of_fac' p' (𝟙 (p.obj x)) e hx₀ hx'
        simpa [gbase, hx', hdomx, Category.assoc] using
          (CategoryTheory.IsHomLift.fac' p' gbase e)
      let hU : (fibreFunctor p p' G over (p.obj x)).FullyFaithful :=
        Classical.choice (hG (p.obj x))
      let e₀ :
          (⟨x, rfl⟩ : Functor.Fiber p (p.obj x)) ⟶
          (⟨x', hdomx⟩ : Functor.Fiber p (p.obj x)) :=
        hU.preimage eF
      have he₀ :
          (fibreFunctor p p' G over (p.obj x)).map e₀ = eF := by
        exact hU.map_preimage eF
      have he₀' : G.map e₀.1 = e := by
        have h' := congrArg (fun k => k.1) he₀
        change G.map e₀.1 = e at h'
        exact h'
      refine ⟨e₀.1 ≫ φ, ?_⟩
      calc
        G.map (e₀.1 ≫ φ) = G.map e₀.1 ≫ G.map φ := by simp
        _ = e ≫ G.map φ := by rw [he₀']
        _ = h := hecomp
    let preimage {x y : S} (h : G.obj x ⟶ G.obj y) : x ⟶ y :=
      Classical.choose (exists_preimage h)
    have hpreimage_map : ∀ {x y : S} (h : G.obj x ⟶ G.obj y),
        G.map (preimage h) = h := by
      intro x y h
      exact Classical.choose_spec (exists_preimage h)
    refine ⟨{ preimage := preimage, map_preimage := hpreimage_map,
      preimage_map := ?_ }⟩
    intro x y f
    apply hfaith.map_injective
    rw [hpreimage_map]

theorem fibredInGroupoids_equivalence_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    G.IsEquivalence ↔
      ∀ U : C, (fibreFunctor p p' G over U).IsEquivalence := by
  sorry

/-- Equivalence over the fixed base, expressed in the category of fibred
category morphisms.  Its isomorphisms are precisely the vertical natural
isomorphisms used as 2-morphisms in the source. -/
def IsEquivalenceOverHom {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) : Prop :=
  ∃ G : FibredCategoryOverHom Y X,
    Nonempty (FibredCategoryOverHom.comp F G ≅
      FibredCategoryOverHom.id X) ∧
      Nonempty (FibredCategoryOverHom.comp G F ≅
        FibredCategoryOverHom.id Y)

theorem equivalence_fibredInGroupoids_is_equivalence_over
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y)
    (hF : Nonempty (overFunctor F.underlying).IsEquivalence) :
    IsEquivalenceOverHom F := by
  sorry

theorem fibredInGroupoids_fullyFaithful_iff_diagonal_isEquivalence
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (overFunctor F.underlying).FullyFaithful ↔
      (fibredCategoryDiagonalFunctor F).IsEquivalence := by
  sorry

/-! ## Equivalences and functor categories -/

/-- Pre- and postcomposition is the functor appearing in the source's
invariance statement for morphism categories. -/
def prePostcompositionFunctor
    {C : Cat.{v, u}} {X₁ X₂ X₃ X₄ : FibredCategoryOver C}
    (φ : FibredCategoryOverHom X₁ X₂)
    (ψ : FibredCategoryOverHom X₃ X₄) :
    FibredCategoryOverHom X₂ X₃ ⥤ FibredCategoryOverHom X₁ X₄ where
  obj α := FibredCategoryOverHom.comp φ
    (FibredCategoryOverHom.comp α ψ)
  map η := fibredWhiskerLeft φ (fibredWhiskerRight η ψ)
  map_id := by
    intro α
    rw [show fibredWhiskerRight (𝟙 α) ψ =
        𝟙 (FibredCategoryOverHom.comp α ψ) by
      exact @Bicategory.id_whiskerRight (FibredCategoryOver C) _
        X₂ X₃ X₄ α ψ]
    exact @Bicategory.whiskerLeft_id (FibredCategoryOver C) _
      X₁ X₂ X₄ φ (FibredCategoryOverHom.comp α ψ)
  map_comp := by
    intro α β γ η θ
    apply OverNatTrans.ext
    change
      (fibredWhiskerLeft φ (fibredWhiskerRight (η ≫ θ) ψ)).toNatTrans =
        (fibredWhiskerLeft φ (fibredWhiskerRight η ψ)).toNatTrans ≫
          (fibredWhiskerLeft φ (fibredWhiskerRight θ ψ)).toNatTrans
    rw [show fibredWhiskerRight (η ≫ θ) ψ =
        fibredWhiskerRight η ψ ≫ fibredWhiskerRight θ ψ by
      exact @Bicategory.comp_whiskerRight (FibredCategoryOver C) _
        X₂ X₃ X₄ η θ ψ]
    exact congrArg (fun q => q.toNatTrans)
      (@Bicategory.whiskerLeft_comp (FibredCategoryOver C) _
        X₁ X₂ X₄ φ (fibredWhiskerRight η ψ) (fibredWhiskerRight θ ψ))

theorem morphisms_equivalent_fibred_groupoids
    {C : Cat.{v, u}} {X₁ X₂ X₃ X₄ : FibredCategoryOver C}
    (hX₁ : IsGroupoidFibredCategoryOver X₁)
    (hX₂ : IsGroupoidFibredCategoryOver X₂)
    (hX₃ : IsGroupoidFibredCategoryOver X₃)
    (hX₄ : IsGroupoidFibredCategoryOver X₄)
    (φ : FibredCategoryOverHom X₁ X₂)
    (ψ : FibredCategoryOverHom X₃ X₄)
    (hφ : Nonempty (overFunctor φ.underlying).IsEquivalence)
    (hψ : Nonempty (overFunctor ψ.underlying).IsEquivalence) :
    (prePostcompositionFunctor φ ψ).IsEquivalence := by
  sorry

/-! ## Inertia, slices, composites, and fibre products -/

theorem inertia_isFibredInGroupoids
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X) :
    (relativeInertiaBase (toBaseFibredHom X).underlying).IsFibredInGroupoids := by
  refine (fibredInGroupoids_iff_fibred_groupoid_fibres
    (relativeInertiaBase (toBaseFibredHom X).underlying)).mpr ?_
  constructor
  · intro U
    constructor
    intro A B f
    have hA :
        (structureFunctor X.underlying).obj A.1.carrier = U := by
      exact A.2
    have hB :
        (structureFunctor X.underlying).obj B.1.carrier = U := by
      exact B.2
    let _ :
        (relativeInertiaBase (toBaseFibredHom X).underlying).IsHomLift
          (𝟙 U) f.1 := f.2
    have hfmap :
        (structureFunctor X.underlying).map f.1.hom =
          eqToHom hA ≫ 𝟙 U ≫ eqToHom hB.symm := by
      simpa [relativeInertiaBase, relativeInertiaStructureMap] using
        (CategoryTheory.IsHomLift.fac'
          (relativeInertiaBase (toBaseFibredHom X).underlying)
          (𝟙 U) f.1)
    let fX :
        (⟨A.1.carrier, hA⟩ :
          Functor.Fiber (structureFunctor X.underlying) U) ⟶
        (⟨B.1.carrier, hB⟩ :
          Functor.Fiber (structureFunctor X.underlying) U) := by
      refine ⟨f.1.hom, ?_⟩
      apply IsHomLift.of_fac' (structureFunctor X.underlying)
        (𝟙 U) f.1.hom hA hB
      exact hfmap
    letI : IsGroupoid (Functor.Fiber (structureFunctor X.underlying) U) :=
      hX U
    letI : IsIso fX := (hX U).all_isIso fX
    letI : IsIso f.1.hom := by
      change IsIso (Functor.Fiber.fiberInclusion.map fX)
      infer_instance
    let g0 : B.1 ⟶ A.1 :=
      { hom := inv f.1.hom
        comm := by
          apply (cancel_mono f.1.hom).1
          simp [Category.assoc, f.1.comm] }
    have hgmap :
        (structureFunctor X.underlying).map (inv f.1.hom) =
          eqToHom hB ≫ 𝟙 U ≫ eqToHom hA.symm := by
      rw [Functor.map_inv, hfmap]
      simp
    have hg0 :
        (relativeInertiaBase (toBaseFibredHom X).underlying).IsHomLift
          (𝟙 U) g0 := by
      apply IsHomLift.of_fac'
        (relativeInertiaBase (toBaseFibredHom X).underlying)
        (𝟙 U) g0 B.2 A.2
      simpa [relativeInertiaBase, relativeInertiaStructureMap, g0] using hgmap
    let g : B ⟶ A := ⟨g0, hg0⟩
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply Functor.Fiber.hom_ext
      apply RelativeInertiaHom.ext
      change f.1.hom ≫ inv f.1.hom = 𝟙 _
      simp
    · apply Functor.Fiber.hom_ext
      apply RelativeInertiaHom.ext
      change inv f.1.hom ≫ f.1.hom = 𝟙 _
      simp
  · exact relativeInertia_isFibred (toBaseFibredHom X)

theorem fibredInGroupoids_over_slice
    {S C : Type*} [Category* S] [Category* C]
    (U : C) (p : S ⥤ C) (p' : S ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p)
    (hp : p.IsFibredInGroupoids) :
    p'.IsFibredInGroupoids := by
  cases factor
  let q := p' ⋙ Over.forget U
  let hq : q.IsFibredInGroupoids := hp
  let _ : q.IsFibered :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.2
  let _ : p'.IsFibered := fibred_over_slice U q p' rfl
  constructor
  · intro V R f x hx
    subst R
    obtain ⟨y, ψ, hψ⟩ :=
      (inferInstance : p'.IsFibered).toIsPreFibered.exists_isCartesian' f
    let _ : p'.IsCartesian f ψ := hψ
    exact ⟨y, ψ, inferInstance⟩
  · intro x y z φ ψ f hcomp
    have hcomp' : f.left ≫ q.map φ = q.map ψ := by
      have h := congrArg (fun k => k.left) hcomp
      simpa [q] using h
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      hq.unique_lift φ ψ hcomp'
    let _ : q.IsHomLift f.left χ := hχ
    have hmap : f.left = q.map χ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift q f.left χ
    have hf : f = p'.map χ := by
      apply Over.OverMorphism.ext
      simpa [q] using hmap
    have hχ' : p'.IsHomLift f χ := by
      rw [hf]
      infer_instance
    refine ⟨χ, ⟨hχ', hχfac⟩, ?_⟩
    intro χ' hχ'
    rcases hχ' with ⟨hχ', hχ'fac⟩
    have hf' : f = p'.map χ' :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p' f χ'
    have hqχ' : q.IsHomLift f.left χ' := by
      have hmap' : f.left = q.map χ' := by
        have h := congrArg (fun k => k.left) hf'
        simpa [q] using h
      rw [hmap']
      infer_instance
    exact hχuniq χ' ⟨hqχ', hχ'fac⟩

theorem fibredInGroupoids_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C)
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids) :
    (p ⋙ q).IsFibredInGroupoids := by
  constructor
  · intro V U f a ha
    change q.obj (p.obj a) = U at ha
    subst U
    obtain ⟨b, ψ, hψ⟩ := hq.exists_lift f rfl
    obtain ⟨a', φ, hφ⟩ := hp.exists_lift ψ rfl
    let _ : q.IsHomLift f ψ := hψ
    let _ : p.IsHomLift ψ φ := hφ
    have hdomP : p.obj a' = b :=
      CategoryTheory.IsHomLift.domain_eq p ψ φ
    subst b
    have hdomQ : q.obj (p.obj a') = V :=
      CategoryTheory.IsHomLift.domain_eq q f ψ
    subst V
    have hmapQ : f = q.map ψ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift q f ψ
    have hmapP : ψ = p.map φ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p ψ φ
    refine ⟨a', φ, ?_⟩
    rw [hmapQ, hmapP]
    infer_instance
  · intro x y z φ ψ f hcomp
    change f ≫ q.map (p.map φ) = q.map (p.map ψ) at hcomp
    obtain ⟨k, ⟨hk, hkfac⟩, hkuniq⟩ :=
      hq.unique_lift (p.map φ) (p.map ψ) hcomp
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      hp.unique_lift φ ψ hkfac
    let _ : q.IsHomLift f k := hk
    let _ : p.IsHomLift k χ := hχ
    have hmapQ : f = q.map k :=
      CategoryTheory.IsHomLift.eq_of_isHomLift q f k
    have hmapP : k = p.map χ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p k χ
    refine ⟨χ, ?_, ?_⟩
    · rw [hmapQ, hmapP]
      infer_instance
    · intro χ' hχ'
      rcases hχ' with ⟨hχ', hχ'fac⟩
      have hχ'q : q.IsHomLift f (p.map χ') := hχ'
      have hχ'fac : p.map χ' ≫ p.map φ = p.map ψ := by
        simpa using congrArg p.map hχ'fac
      have hkχ' : p.map χ' = k :=
        hkuniq (p.map χ') ⟨hχ'q, hχ'fac⟩
      have hχ'base : p.IsHomLift k χ' := by
        rw [← hkχ']
        infer_instance
      exact hχuniq χ' ⟨hχ'base, hχ'fac⟩

theorem fibredInGroupoids_fibre_product_goes_up
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) (hp : p.IsFibredInGroupoids)
    {x y z : S} (f : x ⟶ y) (g : z ⟶ y)
    [HasPullback (p.map f) (p.map g)] :
    ∃ (w : S) (a : w ⟶ z) (b : w ⟶ x),
    p.obj w = pullback (p.map f) (p.map g) ∧
        Functor.IsStronglyCartesian p
          (pullback.snd (p.map f) (p.map g)) a ∧
        IsPullback b a f g := by
  let _ : p.IsFibered :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.2
  let _ : p.IsStronglyCartesian (p.map f) f :=
    fibredInGroupoids_all_morphisms_stronglyCartesian p hp f
  exact fibred_fibre_product_goes_up p f g

/- A natural isomorphism is over a target functor when its components map
to the transported identity in that target. -/
def IsNatIsoOver
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : B ⥤ D) {H K : A ⥤ B} (e : H ≅ K)
    (over : H ⋙ q = K ⋙ q) : Prop :=
  ∀ Z : A, q.map (e.hom.app Z) =
    eqToHom (congrArg (fun L : A ⥤ D => L.obj Z) over)

/- An equivalence over a target functor, with the chosen functor displayed.
The quasi-inverse isomorphisms are required to be over the same target. -/
def IsEquivalenceOverFunctor
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (p : A ⥤ D) (q : B ⥤ D) (h : A ⥤ B) : Prop :=
  ∃ k : B ⥤ A,
    h ⋙ q = p ∧ k ⋙ p = q ∧
      (∃ e : h ⋙ k ≅ 𝟭 A,
        ∃ over : (h ⋙ k) ⋙ p = (𝟭 A) ⋙ p,
          IsNatIsoOver p e over) ∧
      (∃ e : k ⋙ h ≅ 𝟭 B,
        ∃ over : (k ⋙ h) ⋙ q = (𝟭 B) ⋙ q,
          IsNatIsoOver q e over)

/-! ## The amelioration factorization -/

/-- The strengthened package for the explicit comma-category factorization
from Unit 33.  The existing `AmeliorationFactorization` supplies the raw
comma category and its three functors; the additional fields record that the
middle projection is fibred in groupoids, that the first functor is an
equivalence over `C`, and that the second functor is fibred in groupoids. -/
structure GroupoidAmeliorationFactorization
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  data : AmeliorationFactorization F
  middle_groupoid_fibred :
    (ameliorationBase F).IsFibredInGroupoids
  u_equivalence_over_C :
    IsEquivalenceOverFunctor
      (structureFunctor X.underlying) (ameliorationBase F) data.u
  v_groupoid_fibred_over_Y : data.v.IsFibredInGroupoids

abbrev GroupoidAmeliorationCategory
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) :=
  AmeliorationCategory F

theorem groupoidAmelioration_object_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    (ξ : GroupoidAmeliorationCategory F) :
    ∃ U : C,
      IsObjectLift (structureFunctor Y.underlying) U ξ.obj.left ∧
      IsObjectLift (structureFunctor X.underlying) U ξ.obj.right ∧
        IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.obj.hom :=
  amelioration_object_description F ξ

theorem groupoidAmelioration_morphism_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    {ξ ξ' : GroupoidAmeliorationCategory F} (h : ξ ⟶ ξ') :
    h.hom.left ≫ ξ'.obj.hom =
      ξ.obj.hom ≫ (overFunctor F.underlying).map h.hom.right :=
  amelioration_morphism_description F h

theorem groupoidAmelioration_object_isIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y)
    (ξ : GroupoidAmeliorationCategory F) : IsIso ξ.obj.hom := by
  rcases groupoidAmelioration_object_description F ξ with
    ⟨U, hYlift, hXlift, hξ⟩
  let hFX :
      (structureFunctor Y.underlying).obj
          ((overFunctor F.underlying).obj ξ.obj.right) = U :=
    (congrArg
      (fun K : X.underlying.left ⥤ C => K.obj ξ.obj.right)
      (overFunctor_comm F.underlying)).trans hXlift
  let f :
      (⟨ξ.obj.left, hYlift⟩ :
        Functor.Fiber (structureFunctor Y.underlying) U) ⟶
      (⟨(overFunctor F.underlying).obj ξ.obj.right, hFX⟩ :
        Functor.Fiber (structureFunctor Y.underlying) U) :=
    ⟨ξ.obj.hom, hξ⟩
  letI : IsGroupoid (Functor.Fiber (structureFunctor Y.underlying) U) :=
    hY U
  letI : IsIso f := (hY U).all_isIso f
  change IsIso (Functor.Fiber.fiberInclusion.map f)
  infer_instance

theorem ameliorate_morphism_categories_fibred_in_groupoids
    {C : Cat.{v, u}} (X Y : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (GroupoidAmeliorationFactorization F) := by
  sorry

/-! ## Uniqueness of the amelioration -/

/-- A fixed-base form of the 2-commutative diagram used in the final source
lemma.  The two triangle fields are the two 2-commutativity assumptions. -/
structure AmeliorationUniquenessData
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  x_groupoid_fibred_over_C : IsGroupoidFibredCategoryOver X
  y_groupoid_fibred_over_C : IsGroupoidFibredCategoryOver Y
  f : FibredCategoryOverHom X' Y
  g : FibredCategoryOverHom X'' Y
  a : FibredCategoryOverHom X X'
  b : FibredCategoryOverHom X X''
  f_groupoid_fibred_over_Y :
    (overFunctor f.underlying).IsFibredInGroupoids
  g_groupoid_fibred_over_Y :
    (overFunctor g.underlying).IsFibredInGroupoids
  a_equivalence_over_C : IsEquivalenceOverHom a
  b_equivalence_over_C : IsEquivalenceOverHom b
  left_triangle :
    Formalization.Books.Categories.Unit31.IsTwoCommutative
      (C := FibredCategoryOver C) a (FibredCategoryOverHom.id X) f F
  right_triangle :
    Formalization.Books.Categories.Unit31.IsTwoCommutative
      (C := FibredCategoryOver C) b (FibredCategoryOverHom.id X) g F

def underlyingIsoOfFibredHomIso
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (e : F ≅ G) :
    overFunctor F.underlying ≅ overFunctor G.underlying where
  hom := e.hom.toNatTrans
  inv := e.inv.toNatTrans
  hom_inv_id := by
    change e.hom.toNatTrans ≫ e.inv.toNatTrans =
      𝟙 (overFunctor F.underlying)
    exact congrArg
      (fun η : OverNatTrans F.underlying F.underlying => η.toNatTrans)
      e.hom_inv_id
  inv_hom_id := by
    change e.inv.toNatTrans ≫ e.hom.toNatTrans =
      𝟙 (overFunctor G.underlying)
    exact congrArg
      (fun η : OverNatTrans G.underlying G.underlying => η.toNatTrans)
      e.inv_hom_id

theorem amelioration_unique
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    {F : FibredCategoryOverHom X Y}
  (D : AmeliorationUniquenessData F) :
    ∃ h : FibredCategoryOverHom X'' X',
      IsEquivalenceOverFunctor (overFunctor D.g.underlying)
        (overFunctor D.f.underlying) (overFunctor h.underlying) ∧
      Nonempty (FibredCategoryOverHom.comp D.b h ≅ D.a) := by
  sorry

theorem amelioration_unique_when_strictly_commutative
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    {F : FibredCategoryOverHom X Y}
    (D : AmeliorationUniquenessData F)
    (left_strict : CategoryOver.comp D.a.underlying D.f.underlying =
      F.underlying)
    (right_strict : CategoryOver.comp D.b.underlying D.g.underlying =
      F.underlying) :
    ∃ h : FibredCategoryOverHom X'' X',
      IsEquivalenceOverFunctor (overFunctor D.g.underlying)
        (overFunctor D.f.underlying) (overFunctor h.underlying) ∧
      ∃ e : FibredCategoryOverHom.comp D.b h ≅ D.a,
        ∃ overY :
          overFunctor (FibredCategoryOverHom.comp D.b h).underlying ⋙
              overFunctor D.f.underlying =
            overFunctor D.a.underlying ⋙ overFunctor D.f.underlying,
          IsNatIsoOver (overFunctor D.f.underlying)
            (underlyingIsoOfFibredHomIso e) overY := by
  sorry

end
