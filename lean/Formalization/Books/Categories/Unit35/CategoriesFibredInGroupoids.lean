import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
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
open Opposite
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
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres
    (stronglyCartesianSubcategoryProjection p)).mpr
  constructor
  · intro U
    constructor
    intro X Y f
    let _ : (stronglyCartesianSubcategoryProjection p).IsHomLift
        (𝟙 U) f.1 := f.2
    have hmap : IsIso (p.map f.1.hom) := by
      let hd := CategoryTheory.IsHomLift.domain_eq
        (stronglyCartesianSubcategoryProjection p) (𝟙 U) f.1
      let hc := CategoryTheory.IsHomLift.codomain_eq
        (stronglyCartesianSubcategoryProjection p) (𝟙 U) f.1
      let _ : IsIso (eqToHom hd) := (eqToIso hd).isIso_hom
      let _ : IsIso (eqToHom hc.symm) := (eqToIso hc.symm).isIso_hom
      have h := CategoryTheory.IsHomLift.fac'
        (stronglyCartesianSubcategoryProjection p) (𝟙 U) f.1
      change p.map f.1.hom = _ at h
      rw [h]
      simp only [Category.id_comp]
      exact IsIso.comp_isIso' (eqToIso hd).isIso_hom
        (eqToIso hc.symm).isIso_hom
    let _ : IsIso (p.map f.1.hom) := hmap
    let _ : p.IsStronglyCartesian (p.map f.1.hom) f.1.hom := f.1.property
    let _ : IsIso f.1.hom :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map f.1.hom) f.1.hom
    let e : X.1.obj ≅ Y.1.obj := asIso f.1.hom
    have hinvstrong : p.IsStronglyCartesian
        (p.map (inv f.1.hom)) (inv f.1.hom) := by
      let _ : p.IsHomLift (p.map (inv f.1.hom)) e.symm.hom := by
        change p.IsHomLift (p.map (inv f.1.hom)) (inv f.1.hom)
        infer_instance
      exact Functor.IsStronglyCartesian.of_iso p (p.map (inv f.1.hom)) e.symm
    let e' : X.1 ≅ Y.1 := isoMk e f.1.property (by
      change p.IsStronglyCartesian (p.map (inv f.1.hom)) (inv f.1.hom)
      exact hinvstrong)
    have hinv : (stronglyCartesianSubcategoryProjection p).IsHomLift
        (𝟙 U) e'.inv := by
      have hehom : e'.hom = f.1 := by
        apply WideSubcategory.hom_ext
        rfl
      let _ : (stronglyCartesianSubcategoryProjection p).IsHomLift
          (𝟙 U) e'.hom := by
        rw [hehom]
        exact f.2
      exact CategoryTheory.IsHomLift.lift_id_inv
        (stronglyCartesianSubcategoryProjection p) U e'
    exact ⟨⟨⟨e'.inv, hinv⟩, by
      constructor
      · apply Functor.Fiber.hom_ext
        apply WideSubcategory.hom_ext
        change f.1.hom ≫ e'.inv.hom = 𝟙 X.1.obj
        exact congrArg (fun k => k.hom) e'.hom_inv_id
      · apply Functor.Fiber.hom_ext
        apply WideSubcategory.hom_ext
        change e'.inv.hom ≫ f.1.hom = 𝟙 Y.1.obj
        exact congrArg (fun k => k.hom) e'.inv_hom_id⟩⟩
  · apply Functor.IsFibered.of_exists_isStronglyCartesian
    intro x R f
    obtain ⟨y, φ, hφ⟩ := Functor.IsPreFibered.exists_isCartesian' (p := p) f
    let _ : p.IsCartesian f φ := hφ
    let _ : p.IsHomLift f φ := inferInstance
    have hd := CategoryTheory.IsHomLift.domain_eq p f φ
    cases hd
    let _ : p.IsCartesian f φ := hφ
    let _ : p.IsHomLift f φ := inferInstance
    change p.obj y ⟶ p.obj ((stronglyCartesianSubcategoryInclusion p).obj x) at f
    have hf : f = p.map φ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p f φ
    have hstrong : p.IsStronglyCartesian f φ :=
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p f φ
    let _ : p.IsStronglyCartesian f φ := hstrong
    have hstrong' : p.IsStronglyCartesian (p.map φ) φ := by
      rw [← hf]
      infer_instance
    let _ : p.IsStronglyCartesian (p.map φ) φ := hstrong'
    let y' : StronglyCartesianSubcategory p := ⟨y⟩
    let φ' : y' ⟶ x := ⟨φ, by
      change p.IsStronglyCartesian (p.map φ) φ
      infer_instance⟩
    refine ⟨y', φ', ?_⟩
    have hφ' : (stronglyCartesianSubcategoryProjection p).IsHomLift f φ' := by
      dsimp [stronglyCartesianSubcategoryProjection,
        stronglyCartesianSubcategoryInclusion, y', φ']
      rw [hf]
      exact Functor.IsHomLift.map φ'
    let _ : (stronglyCartesianSubcategoryProjection p).IsHomLift f φ' := hφ'
    refine { toIsHomLift := hφ', universal_property' := ?_ }
    intro a g τ hτ
    change p.obj a.obj ⟶ p.obj y at g
    have hτeq : g ≫ f = p.map τ.hom := by
      have h := CategoryTheory.IsHomLift.eq_of_isHomLift
        (stronglyCartesianSubcategoryProjection p) (g ≫ f) τ
      change g ≫ f = p.map τ.hom at h
      exact h
    have hτp : p.IsHomLift (g ≫ f) τ.hom := by
      rw [hτeq]
      exact Functor.IsHomLift.map τ.hom
    let _ : p.IsHomLift (g ≫ f) τ.hom := hτp
    obtain ⟨δ, ⟨hδ, hδcomp⟩, hδunique⟩ :=
      @Functor.IsStronglyCartesian.universal_property _ _ _ _ p
        _ _ _ _ f φ hstrong _ _ g (g ≫ f) rfl τ.hom hτp
    have hτstrong : p.IsStronglyCartesian (g ≫ f) (δ ≫ φ) := by
      rw [hδcomp, hτeq]
      exact τ.property
    have hδstrong : p.IsStronglyCartesian g δ := by
      let _ : p.IsStronglyCartesian (g ≫ f) (δ ≫ φ) := hτstrong
      let _ : p.IsHomLift g δ := hδ
      exact Functor.IsStronglyCartesian.of_comp
        (p := p) (f := g) (φ := δ) (g := f) (ψ := φ)
    let _ : p.IsHomLift g δ := hδ
    let hδmap : g = p.map δ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p g δ
    have hδstrong' : p.IsStronglyCartesian (p.map δ) δ := by
      rw [← hδmap]
      exact hδstrong
    let δ' : a ⟶ y' := ⟨δ, hδstrong'⟩
    have hδq : (stronglyCartesianSubcategoryProjection p).IsHomLift g δ' := by
      dsimp [stronglyCartesianSubcategoryProjection,
        stronglyCartesianSubcategoryInclusion, y', δ']
      rw [hδmap]
      simpa [stronglyCartesianSubcategoryProjection,
        stronglyCartesianSubcategoryInclusion, y', δ'] using
        (Functor.IsHomLift.map
          (p := stronglyCartesianSubcategoryProjection p) δ')
    refine ⟨δ', ⟨hδq, ?_⟩, ?_⟩
    · apply WideSubcategory.hom_ext
      exact hδcomp
    · intro δ' hδ'
      apply WideSubcategory.hom_ext
      rcases hδ' with ⟨hδ'lift, hδ'comp⟩
      let _ : (stronglyCartesianSubcategoryProjection p).IsHomLift g δ' := hδ'lift
      have hδ'map : g = p.map δ'.hom := by
        exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
          (stronglyCartesianSubcategoryProjection p) _ _ g δ' hδ'lift
      have hδ'lift' : p.IsHomLift g δ'.hom := by
        rw [hδ'map]
        exact Functor.IsHomLift.map δ'.hom
      have hδ'comp' : δ'.hom ≫ φ = τ.hom := by
        have h := congrArg (fun k => k.hom) hδ'comp
        change δ'.hom ≫ φ = τ.hom at h
        exact h
      exact hδunique δ'.hom ⟨hδ'lift', hδ'comp'⟩

/-! ## Examples -/

theorem groupHomomorphism_fibredInGroupoids_iff_surjective
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    (MonoidHom.toFunctor p).IsFibredInGroupoids ↔ Function.Surjective p := by
  constructor
  · intro hp h
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift (SingleObj.toEnd H h) rfl
    let _ : (MonoidHom.toFunctor p).IsHomLift (SingleObj.toEnd H h) φ := hφ
    have hmap := CategoryTheory.IsHomLift.eq_of_isHomLift
      (MonoidHom.toFunctor p) (SingleObj.toEnd H h) φ
    refine ⟨φ, ?_⟩
    exact hmap.symm
  · intro hs
    refine { exists_lift := ?_, unique_lift := ?_ }
    · intro V U f x hx
      obtain ⟨g, hg⟩ := hs f
      refine ⟨SingleObj.star G, SingleObj.toEnd G g, ?_⟩
      let _ : (MonoidHom.toFunctor p).IsHomLift f (SingleObj.toEnd G g) := by
        rw [← hg]
        exact Functor.IsHomLift.map _
      exact inferInstance
    · intro x y z φ ψ f hcomp
      obtain ⟨g, hg⟩ := hs f
      let _ : IsIso φ := inferInstance
      let χ : z ⟶ y := ψ ≫ inv φ
      have hχmap : f = (MonoidHom.toFunctor p).map χ := by
        apply (cancel_mono ((MonoidHom.toFunctor p).map φ)).1
        simpa [χ, Functor.map_comp, Category.assoc] using hcomp
      let _ : (MonoidHom.toFunctor p).IsHomLift f χ := by
        rw [hχmap]
        exact Functor.IsHomLift.map _
      refine ⟨χ, ⟨inferInstance, by simp [χ]⟩, ?_⟩
      intro χ' hχ'
      apply (cancel_mono φ).1
      calc
        χ' ≫ φ = ψ := hχ'.2
        _ = χ ≫ φ := by simp [χ]

theorem groupHomomorphism_fibre_is_kernel_groupoid
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    Nonempty
      (Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ≌
        SingleObj (MonoidHom.ker p)) := by
  let F : Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ⥤
      SingleObj (MonoidHom.ker p) := {
    obj _ := SingleObj.star (MonoidHom.ker p)
    map f := ⟨f.1, by
      let _ : (MonoidHom.toFunctor p).IsHomLift
          (𝟙 (SingleObj.star H)) f.1 := f.2
      have h := CategoryTheory.IsHomLift.eq_of_isHomLift
        (MonoidHom.toFunctor p) (𝟙 (SingleObj.star H)) f.1
      exact h.symm⟩
    map_id := by
      intro X
      apply Subtype.ext
      change (𝟙 X.1 : G) = 1
      rw [SingleObj.id_as_one]
    map_comp := by
      intro X Y Z f g
      apply Subtype.ext
      change g.1 * f.1 = g.1 * f.1
      rfl }
  let _ : F.Faithful := {
    map_injective := by
      intro X Y f g h
      apply Functor.Fiber.hom_ext
      change f.1 = g.1
      exact congrArg (fun z : MonoidHom.ker p => z.1) h }
  let _ : F.Full := {
    map_surjective := by
      intro X Y f
      refine ⟨⟨f.1, ?_⟩, ?_⟩
      · change (MonoidHom.toFunctor p).IsHomLift
          (𝟙 (SingleObj.star H)) f.1
        apply CategoryTheory.IsHomLift.of_fac'
          (MonoidHom.toFunctor p) (𝟙 (SingleObj.star H))
            (f.1 : G) X.2 Y.2
        have hf : p f.1 = 1 := f.2
        simpa [MonoidHom.toFunctor, SingleObj.mapHom, SingleObj.id_as_one,
          SingleObj.comp_as_mul] using hf
      · apply Subtype.ext
        rfl }
  let _ : F.EssSurj := {
    mem_essImage := by
      intro X
      refine ⟨⟨SingleObj.star G, rfl⟩, ?_⟩
      exact ⟨Iso.refl _⟩ }
  let _ : F.IsEquivalence := {}
  exact ⟨F.asEquivalence⟩

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
  let _ : p.IsHomLift f φ := hφ
  let _ : p.IsHomLift f ψ := hψ
  let _ : Functor.IsStronglyCartesian p (p.map k) k :=
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
    let _ : IsGroupoid (Functor.Fiber (structureFunctor Y.underlying) U) := hY U
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
  let _ : IsIso η.hom := fibredInGroupoids_two_morphism_isIso
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

/- Proof roadmap: take the `FibredTwoFibreProduct` supplied by Unit 33, identify
its fibre over `U` with the iso-comma of the fibre functors of `F` and `G`,
install the groupoid instance on that iso-comma from `hX U`, `hY U`, and
`hS U`, and package those instances as `fibres_are_groupoids`.  The missing
API is the strict over-base equivalence between these two fibre models. -/
theorem categoriesFibredInGroupoids_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInGroupoidsTwoFibreProduct F G) := by
  refine ⟨{
    product := canonicalFibredTwoFibreProduct X Y S F G
    fibres_are_groupoids := ?_ }⟩
  intro U
  obtain ⟨e⟩ := twoFibreProductOver_fibre_equivalent
    F.underlying G.underlying U
  let _ : IsGroupoid
      (IsoComma (overMorphismFiberFunctor F.underlying U)
        (overMorphismFiberFunctor G.underlying U)) := by
    constructor
    intro a b f
    let _ : IsIso f.hom.left := (hX U).all_isIso _
    let _ : IsIso f.hom.right := (hY U).all_isIso _
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
  let _ : e.functor.IsEquivalence := by infer_instance
  refine { all_isIso := ?_ }
  intro a b f
  let _ : IsIso (e.functor.map f) :=
    (inferInstance : IsGroupoid
      (IsoComma (overMorphismFiberFunctor F.underlying U)
        (overMorphismFiberFunctor G.underlying U))).all_isIso _
  exact e.fullyFaithfulFunctor.isIso_of_isIso_map f

/-- The two descriptions of the category-valued 2-fibre product in the
source are canonically equivalent for categories fibred in groupoids: the
fixed-base presentation remembers a base object, while `IsoComma` remembers
only the isomorphism.

Proof roadmap: forget the common base object to define the forward functor;
for the inverse, transport one leg along the displayed isomorphism using a
chosen cartesian lift in `S`; prove the two composites naturally isomorphic
using uniqueness of cartesian lifts.  Finally show the construction is
independent of the chosen lifts.  This awaits a reusable strict over-base
equivalence/transport API. -/
theorem twoFibreProductOverCategory_canonically_equivalent
    {C : Cat.{v, u}} {X Y S : FibredCategoryOver C}
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty
      (TwoFibreProductOverCategory F.underlying G.underlying ≌
        IsoComma (overFunctor F.underlying) (overFunctor G.underlying)) := by
  let pX := structureFunctor X.underlying
  let pY := structureFunctor Y.underlying
  let pS := structureFunctor S.underlying
  let ι : TwoFibreProductOverCategory F.underlying G.underlying ⥤
      IsoComma (overFunctor F.underlying) (overFunctor G.underlying) :=
    (TwoFibreProductOverProperty F.underlying G.underlying).ι
  let hι : ι.IsEquivalence := by
    refine { faithful := inferInstance, full := inferInstance, essSurj := ?_ }
    constructor
    intro ξ
    let hFx : pS.obj ((overFunctor F.underlying).obj ξ.obj.left) =
        pX.obj ξ.obj.left :=
      Functor.congr_obj (overFunctor_comm F.underlying) ξ.obj.left
    let hGy : pS.obj ((overFunctor G.underlying).obj ξ.obj.right) =
        pY.obj ξ.obj.right :=
      Functor.congr_obj (overFunctor_comm G.underlying) ξ.obj.right
    let baseα : pX.obj ξ.obj.left ⟶ pY.obj ξ.obj.right :=
      eqToHom hFx.symm ≫ pS.map ξ.obj.hom ≫ eqToHom hGy
    obtain ⟨y', φ, hφ⟩ :=
      (groupoidFibredCategoryOver_isFibredInGroupoids Y hY).exists_lift
        baseα rfl
    let hdom : pY.obj y' = pX.obj ξ.obj.left :=
      CategoryTheory.IsHomLift.domain_eq pY baseα φ
    let _ : pY.IsHomLift baseα φ := hφ
    have hφmap : pY.map φ = eqToHom hdom ≫ baseα := by
      simpa using CategoryTheory.IsHomLift.fac' pY baseα φ
    let _ : IsIso ξ.obj.hom := ξ.property
    let _ : IsIso baseα := by
      dsimp [baseα]
      infer_instance
    let _ : IsIso (pY.map φ) := by
      rw [hφmap]
      infer_instance
    let _ : pY.IsStronglyCartesian (pY.map φ) φ :=
      fibredInGroupoids_all_morphisms_stronglyCartesian pY
        (groupoidFibredCategoryOver_isFibredInGroupoids Y hY) φ
    let _ : IsIso φ := stronglyCartesian_of_base_isIso pY (pY.map φ) φ
    let hGy' : pS.obj ((overFunctor G.underlying).obj y') =
        pX.obj ξ.obj.left :=
      (Functor.congr_obj (overFunctor_comm G.underlying) y').trans hdom
    let β : (overFunctor F.underlying).obj ξ.obj.left ⟶
        (overFunctor G.underlying).obj y' :=
      ξ.obj.hom ≫ inv ((overFunctor G.underlying).map φ)
    let _ : IsIso β := by
      dsimp [β]
      infer_instance
    have hβ : pS.IsHomLift (𝟙 (pX.obj ξ.obj.left)) β := by
      apply CategoryTheory.IsHomLift.of_fac' pS (𝟙 (pX.obj ξ.obj.left)) β
        hFx hGy'
      have hGφ : pS.map ((overFunctor G.underlying).map φ) =
          eqToHom (Functor.congr_obj (overFunctor_comm G.underlying) y') ≫
            pY.map φ ≫
              eqToHom (Functor.congr_obj (overFunctor_comm G.underlying)
                ξ.obj.right).symm := by
        exact Functor.congr_hom (overFunctor_comm G.underlying) φ
      simp [Functor.map_comp, Functor.map_inv, hGφ, hφmap, baseα, hGy', β,
        Category.assoc, eqToHom_trans]
    let z : TwoFibreProductOverCategory F.underlying G.underlying :=
      { obj :=
          { obj := { left := ξ.obj.left, right := y', hom := β }
            property := by
              change IsIso β
              infer_instance }
        property := ⟨pX.obj ξ.obj.left, rfl, hdom, hβ⟩ }
    refine ⟨z, ?_⟩
    refine ⟨ObjectProperty.isoMk _
      (Comma.isoMk (Iso.refl _) (asIso φ) ?_)⟩
    change (overFunctor F.underlying).map (𝟙 ξ.obj.left) ≫ ξ.obj.hom =
      β ≫ (overFunctor G.underlying).map φ
    simp [β]
  exact ⟨@Functor.asEquivalence _ _ _ _ ι hι⟩

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
    let _ : G.Faithful := hG
    constructor
    intro x y f g hfg
    apply Functor.Fiber.hom_ext
    change f.1 = g.1
    apply hG.map_injective
    exact congrArg (fun k => k.1) hfg
  · intro hG
    let _ : p.IsFibredInGroupoids := hp
    let _ : p'.IsFibredInGroupoids := hp'
    constructor
    intro X Y f g hfg
    have hbase : p.map f = p.map g := by
      have hf_over : p'.map (G.map f) =
          eqToHom (Functor.congr_obj over X) ≫ p.map f ≫
            eqToHom (Functor.congr_obj over Y).symm := by
        simpa only [Functor.comp_map] using Functor.congr_hom over f
      have hg_over : p'.map (G.map g) =
          eqToHom (Functor.congr_obj over X) ≫ p.map g ≫
            eqToHom (Functor.congr_obj over Y).symm := by
        simpa only [Functor.comp_map] using Functor.congr_hom over g
      apply (cancel_epi (eqToHom (Functor.congr_obj over X))).1
      apply (cancel_mono (eqToHom (Functor.congr_obj over Y).symm)).1
      calc
        (eqToHom (Functor.congr_obj over X) ≫ p.map f) ≫
              eqToHom (Functor.congr_obj over Y).symm = p'.map (G.map f) := by
          simpa [Category.assoc] using hf_over.symm
        _ = p'.map (G.map g) := by rw [hfg]
        _ = (eqToHom (Functor.congr_obj over X) ≫ p.map g) ≫
              eqToHom (Functor.congr_obj over Y).symm := by
          simpa [Category.assoc] using hg_over
    obtain ⟨Z, φ, hφ⟩ := hp.exists_lift (p.map f) rfl
    let _ : p.IsHomLift (p.map f) φ := hφ
    have hdom : p.obj Z = p.obj X :=
      CategoryTheory.IsHomLift.domain_eq p (p.map f) φ
    have hφmap : p.map φ = eqToHom hdom ≫ p.map f := by
      simpa using CategoryTheory.IsHomLift.fac' p (p.map f) φ
    have hfactor : eqToHom hdom.symm ≫ p.map φ = p.map f := by
      rw [hφmap]
      simp
    obtain ⟨χ, ⟨hχ, hχcomp⟩, _⟩ :=
      fibredInGroupoids_unique_lift p φ f hfactor
    have hfactor' : eqToHom hdom.symm ≫ p.map φ = p.map g :=
      hfactor.trans hbase
    obtain ⟨χ', ⟨hχ', hχ'comp⟩, _⟩ :=
      fibredInGroupoids_unique_lift p φ g hfactor'
    have hχfiber : p.IsHomLift (𝟙 (p.obj X)) χ := by
      let _ : p.IsHomLift (eqToHom hdom.symm) χ := hχ
      apply CategoryTheory.IsHomLift.of_fac' p (𝟙 (p.obj X)) χ rfl hdom
      simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift
        p (eqToHom hdom.symm) χ).symm
    have hχ'fiber : p.IsHomLift (𝟙 (p.obj X)) χ' := by
      let _ : p.IsHomLift (eqToHom hdom.symm) χ' := hχ'
      apply CategoryTheory.IsHomLift.of_fac' p (𝟙 (p.obj X)) χ' rfl hdom
      simpa using (CategoryTheory.IsHomLift.eq_of_isHomLift
        p (eqToHom hdom.symm) χ').symm
    have hGχ : G.map χ = G.map χ' := by
      let _ : p'.IsStronglyCartesian
          (p'.map (G.map φ)) (G.map φ) :=
        fibredInGroupoids_all_morphisms_stronglyCartesian p' hp' (G.map φ)
      have hχmap : p'.map (G.map χ) = p'.map (G.map χ') := by
        have hχ_over : p'.map (G.map χ) =
            eqToHom (Functor.congr_obj over X) ≫ p.map χ ≫
              eqToHom (Functor.congr_obj over Z).symm := by
          simpa only [Functor.comp_map] using Functor.congr_hom over χ
        have hχ'_over : p'.map (G.map χ') =
            eqToHom (Functor.congr_obj over X) ≫ p.map χ' ≫
              eqToHom (Functor.congr_obj over Z).symm := by
          simpa only [Functor.comp_map] using Functor.congr_hom over χ'
        calc
          p'.map (G.map χ) =
              eqToHom (Functor.congr_obj over X) ≫ p.map χ ≫
                eqToHom (Functor.congr_obj over Z).symm := hχ_over
          _ = eqToHom (Functor.congr_obj over X) ≫
              p.map χ' ≫ eqToHom (Functor.congr_obj over Z).symm := by
            let _ : p.IsHomLift (eqToHom hdom.symm) χ := hχ
            let _ : p.IsHomLift (eqToHom hdom.symm) χ' := hχ'
            have hχ_base : p.map χ = p.map χ' :=
              (CategoryTheory.IsHomLift.eq_of_isHomLift
                p (eqToHom hdom.symm) χ).symm.trans
                (CategoryTheory.IsHomLift.eq_of_isHomLift
                  p (eqToHom hdom.symm) χ')
            rw [hχ_base]
          _ = p'.map (G.map χ') := hχ'_over.symm
      let _ : p'.IsHomLift (p'.map (G.map χ')) (G.map χ) := by
        rw [← hχmap]
        exact Functor.IsHomLift.map _
      let _ : p'.IsHomLift (p'.map (G.map χ')) (G.map χ') :=
        Functor.IsHomLift.map _
      apply Functor.IsStronglyCartesian.ext p'
        (p'.map (G.map φ)) (G.map φ) (p'.map (G.map χ'))
      calc
        G.map χ ≫ G.map φ = G.map f := by
          simpa only [Functor.map_comp] using congrArg G.map hχcomp
        _ = G.map g := hfg
        _ = G.map χ' ≫ G.map φ := by
          simpa only [Functor.map_comp] using (congrArg G.map hχ'comp).symm
    let x₀ : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
    let z₀ : Functor.Fiber p (p.obj X) := ⟨Z, hdom⟩
    let χ₀ : x₀ ⟶ z₀ := ⟨χ, hχfiber⟩
    let χ₀' : x₀ ⟶ z₀ := ⟨χ', hχ'fiber⟩
    have hχ₀ : χ₀ = χ₀' := by
      apply (hG (p.obj X)).map_injective
      apply Functor.Fiber.hom_ext
      change G.map χ = G.map χ'
      exact hGχ
    have hχeq : χ = χ' := congrArg (fun k => k.1) hχ₀
    calc
      f = χ ≫ φ := hχcomp.symm
      _ = χ' ≫ φ := by rw [hχeq]
      _ = g := hχ'comp

theorem fibredInGroupoids_fullyFaithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    Nonempty G.FullyFaithful ↔
      ∀ U : C, Nonempty (fibreFunctor p p' G over U).FullyFaithful := by
  constructor
  · rintro ⟨hG⟩ U
    let _ : G.FullyFaithful := hG
    let _ : G.Full := hG.full
    let _ : G.Faithful := hG.faithful
    let hFiberFaithful : (fibreFunctor p p' G over U).Faithful := by
      exact (fibredInGroupoids_faithful_iff_fibrewise
        p p' G over hp hp').mp hG.faithful U
    let hFiberFull : (fibreFunctor p p' G over U).Full := by
      constructor
      intro x y f
      obtain ⟨φ, hφ⟩ := hG.map_surjective f.1
      let hx₀ : p'.obj (G.obj x.1) = p.obj x.1 :=
        Functor.congr_obj over x.1
      let hy₀ : p'.obj (G.obj y.1) = p.obj y.1 :=
        Functor.congr_obj over y.1
      have hφmap : p.map φ = eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm := by
        let _ : p'.IsHomLift (𝟙 U) f.1 := f.2
        have hφover : p'.map (G.map φ) =
            eqToHom hx₀ ≫ p.map φ ≫ eqToHom hy₀.symm := by
          exact Functor.congr_hom over φ
        have hf : p'.map f.1 =
            eqToHom (hx₀.trans x.2) ≫ 𝟙 U ≫
              eqToHom (hy₀.trans y.2).symm :=
          CategoryTheory.IsHomLift.fac' p' (𝟙 U) f.1
        have hφmap' : p'.map (G.map φ) = p'.map f.1 :=
          congrArg (fun q : G.obj x.1 ⟶ G.obj y.1 => p'.map q) hφ
        apply (cancel_epi (eqToHom hx₀)).1
        apply (cancel_mono (eqToHom hy₀.symm)).1
        have hleft : (eqToHom hx₀ ≫ p.map φ) ≫ eqToHom hy₀.symm =
            p'.map f.1 := by
          have h₁ : (eqToHom hx₀ ≫ p.map φ) ≫ eqToHom hy₀.symm =
              p'.map (G.map φ) := by
            simpa [Category.assoc] using hφover.symm
          exact h₁.trans hφmap'
        have hright : p'.map f.1 =
            (eqToHom hx₀ ≫
              (eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm)) ≫
                eqToHom hy₀.symm := by
          have heq :
              eqToHom (hx₀.trans x.2) ≫ 𝟙 U ≫
                  eqToHom (hy₀.trans y.2).symm =
                (eqToHom hx₀ ≫
                  (eqToHom x.2 ≫ 𝟙 U ≫ eqToHom y.2.symm)) ≫
                    eqToHom hy₀.symm := by
            simp [eqToHom_trans]
          exact hf.trans heq
        exact hleft.trans hright
      have hφfiber : p.IsHomLift (𝟙 U) φ := by
        apply CategoryTheory.IsHomLift.of_fac' p (𝟙 U) φ x.2 y.2
        exact hφmap
      refine ⟨⟨φ, hφfiber⟩, ?_⟩
      apply Functor.Fiber.hom_ext
      change G.map φ = f.1
      exact hφ
    let preimage {x y : Functor.Fiber p U}
        (f : (fibreFunctor p p' G over U).obj x ⟶
          (fibreFunctor p p' G over U).obj y) : x ⟶ y :=
      Classical.choose (hFiberFull.map_surjective f)
    have map_preimage {x y : Functor.Fiber p U}
        (f : (fibreFunctor p p' G over U).obj x ⟶
          (fibreFunctor p p' G over U).obj y) :
        (fibreFunctor p p' G over U).map (preimage f) = f := by
      exact Classical.choose_spec (hFiberFull.map_surjective f)
    refine ⟨Functor.FullyFaithful.mk preimage ?_ ?_⟩
    · intro x y f
      exact map_preimage f
    · intro x y f
      apply hFiberFaithful.map_injective
      exact map_preimage _
  · intro hG
    let _ : p.IsFibredInGroupoids := hp
    let _ : p'.IsFibredInGroupoids := hp'
    have hGfaithful : G.Faithful :=
      (fibredInGroupoids_faithful_iff_fibrewise
        p p' G over hp hp').mpr (by
          intro U
          let hFiber : (fibreFunctor p p' G over U).FullyFaithful :=
            Classical.choice (hG U)
          exact hFiber.faithful)
    have hGfull : G.Full := by
      constructor
      · intro X Y f
        let hx : p'.obj (G.obj X) = p.obj X := Functor.congr_obj over X
        let hy : p'.obj (G.obj Y) = p.obj Y := Functor.congr_obj over Y
        let k : p.obj X ⟶ p.obj Y :=
          eqToHom hx.symm ≫ p'.map f ≫ eqToHom hy
        obtain ⟨Z, φ, hφ⟩ := hp.exists_lift k rfl
        let _ : p.IsHomLift k φ := hφ
        have hdom : p.obj Z = p.obj X :=
          CategoryTheory.IsHomLift.domain_eq p k φ
        have hφmap : p.map φ = eqToHom hdom ≫ k := by
          simpa using CategoryTheory.IsHomLift.fac' p k φ
        let hz : p'.obj (G.obj Z) = p.obj Z := Functor.congr_obj over Z
        let U := p.obj X
        let hbaseEq : p'.obj (G.obj X) = p'.obj (G.obj Z) :=
          hx.trans (hdom.symm.trans hz.symm)
        let gbase : p'.obj (G.obj X) ⟶ p'.obj (G.obj Z) :=
          eqToHom hbaseEq
        have hGφmap : p'.map (G.map φ) =
            eqToHom hz ≫ p.map φ ≫ eqToHom hy.symm := by
          exact Functor.congr_hom over φ
        have hfactor : gbase ≫ p'.map (G.map φ) = p'.map f := by
          rw [hGφmap, hφmap]
          dsimp [gbase, hbaseEq, k]
          simp [eqToHom_trans, Category.assoc]
        let _ : p'.IsStronglyCartesian
            (p'.map (G.map φ)) (G.map φ) :=
          fibredInGroupoids_all_morphisms_stronglyCartesian p' hp' (G.map φ)
        let _ : p'.IsHomLift (gbase ≫ p'.map (G.map φ)) f := by
          rw [hfactor]
          exact Functor.IsHomLift.map _
        obtain ⟨δ, ⟨hδ, hδcomp⟩, _⟩ :=
          Functor.IsStronglyCartesian.universal_property'
            (p := p') (φ := G.map φ) (p'.map (G.map φ)) gbase f
        let x₀ : Functor.Fiber p U := ⟨X, rfl⟩
        let z₀ : Functor.Fiber p U := ⟨Z, hdom⟩
        have hδfiber : p'.IsHomLift (𝟙 U) δ := by
          apply CategoryTheory.IsHomLift.of_fac' p' (𝟙 U) δ hx
            (hz.trans hdom)
          let _ : p'.IsHomLift gbase δ := hδ
          have hδmap : gbase = p'.map δ :=
            CategoryTheory.IsHomLift.eq_of_isHomLift p' gbase δ
          calc
            p'.map δ = gbase := hδmap.symm
            _ = eqToHom hx ≫ 𝟙 U ≫ eqToHom (hz.trans hdom).symm := by
              dsimp [gbase, hbaseEq]
              have hEq : eqToHom hbaseEq =
                  eqToHom hx ≫ eqToHom (hz.trans hdom).symm := by
                rw [← eqToHom_trans]
              change eqToHom hbaseEq =
                eqToHom hx ≫ (𝟙 U ≫ eqToHom (hz.trans hdom).symm)
              rw [Category.id_comp]
              exact hEq
        let δ₀ : (fibreFunctor p p' G over U).obj x₀ ⟶
            (fibreFunctor p p' G over U).obj z₀ := ⟨δ, hδfiber⟩
        let hFiber : (fibreFunctor p p' G over U).FullyFaithful :=
          Classical.choice (hG U)
        obtain ⟨χ₀, hχ₀⟩ := hFiber.map_surjective δ₀
        let χ : X ⟶ Z := χ₀.1
        have hχmap : G.map χ = δ := by
          have h := congrArg (fun t => t.1) hχ₀
          exact h
        refine ⟨χ ≫ φ, ?_⟩
        simp only [Functor.map_comp, hχmap]
        exact hδcomp
    let preimage {X Y : S} (f : G.obj X ⟶ G.obj Y) : X ⟶ Y :=
      Classical.choose (hGfull.map_surjective f)
    have map_preimage {X Y : S} (f : G.obj X ⟶ G.obj Y) :
        G.map (preimage f) = f :=
      Classical.choose_spec (hGfull.map_surjective f)
    refine ⟨Functor.FullyFaithful.mk preimage ?_ ?_⟩
    · intro X Y f
      exact map_preimage f
    · intro X Y f
      apply hGfaithful.map_injective
      exact map_preimage _

theorem fibredInGroupoids_equivalence_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    G.IsEquivalence ↔
      ∀ U : C, (fibreFunctor p p' G over U).IsEquivalence := by
  classical
  have hp'group : ∀ U : C, IsGroupoid (Functor.Fiber p' U) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres p').mp hp' |>.1
  constructor
  · intro hG U
    let _ : G.IsEquivalence := hG
    let _ : G.Full := hG.full
    let _ : G.Faithful := hG.faithful
    have hGff : Nonempty G.FullyFaithful :=
      ⟨Functor.FullyFaithful.ofFullyFaithful G⟩
    let hFiberFF : (fibreFunctor p p' G over U).FullyFaithful :=
      Classical.choice
        ((fibredInGroupoids_fullyFaithful_iff_fibrewise
          p p' G over hp hp').mp hGff U)
    let _ : (fibreFunctor p p' G over U).FullyFaithful := hFiberFF
    let _ : (fibreFunctor p p' G over U).Full := hFiberFF.full
    let _ : (fibreFunctor p p' G over U).Faithful := hFiberFF.faithful
    let _ : G.EssSurj := hG.essSurj
    let _ : (fibreFunctor p p' G over U).EssSurj := by
      constructor
      intro y
      obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage G y.1
      let hx : p'.obj (G.obj x) = p.obj x :=
        congrArg (fun K : S ⥤ C => K.obj x) over
      let f : U ⟶ p.obj x :=
        eqToHom y.2.symm ≫ p'.map e.inv ≫ eqToHom hx
      let _ : IsIso f := by
        dsimp [f]
        infer_instance
      obtain ⟨x', φ, hφ⟩ := hp.exists_lift f rfl
      let _ : p.IsHomLift f φ := hφ
      have hdom : p.obj x' = U :=
        CategoryTheory.IsHomLift.domain_eq p f φ
      have hφmap : p.map φ = eqToHom hdom ≫ f := by
        simpa using CategoryTheory.IsHomLift.fac' p f φ
      let _ : IsIso (p.map φ) := by
        rw [hφmap]
        infer_instance
      let _ : p.IsStronglyCartesian (p.map φ) φ :=
        fibredInGroupoids_all_morphisms_stronglyCartesian p hp φ
      let _ : IsIso φ :=
        Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ
      let hx' : p'.obj (G.obj x') = p.obj x' :=
        congrArg (fun K : S ⥤ C => K.obj x') over
      let hxU : p'.obj (G.obj x') = U := hx'.trans hdom
      let xU : Functor.Fiber p U := ⟨x', hdom⟩
      let _ : IsGroupoid (Functor.Fiber p' U) := hp'group U
      let k : (fibreFunctor p p' G over U).obj xU ⟶ y := by
        refine ⟨G.map φ ≫ e.hom, ?_⟩
        apply CategoryTheory.IsHomLift.of_fac' p' (𝟙 U)
          (G.map φ ≫ e.hom) hxU y.2
        have hGφ : p'.map (G.map φ) =
            eqToHom hx' ≫ p.map φ ≫ eqToHom hx.symm :=
          Functor.congr_hom over φ
        rw [Functor.map_comp, hGφ, hφmap]
        dsimp [f, hxU]
        simp [Category.assoc]
      let _ : IsIso k := by
        exact (hp'group U).all_isIso k
      exact ⟨xU, ⟨asIso k⟩⟩
    exact {
      faithful := hFiberFF.faithful
      full := hFiberFF.full
      essSurj := inferInstance
    }
  · intro hG
    have hGff : Nonempty G.FullyFaithful :=
      (fibredInGroupoids_fullyFaithful_iff_fibrewise
        p p' G over hp hp').mpr (by
          intro U
          let _ : (fibreFunctor p p' G over U).IsEquivalence := hG U
          exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩)
    let hGff' : G.FullyFaithful := Classical.choice hGff
    have hGess : G.EssSurj := by
      constructor
      intro y
      let U := p'.obj y
      let _ : (fibreFunctor p p' G over U).IsEquivalence := hG U
      obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
        (fibreFunctor p p' G over U) ⟨y, rfl⟩
      refine ⟨x.1, ?_⟩
      exact ⟨(Functor.Fiber.fiberInclusion
        (p := p') (S := U)).mapIso e⟩
    exact {
      faithful := hGff'.faithful
      full := hGff'.full
      essSurj := hGess
    }

private theorem canonicalFibredTwoFibreProduct_fibres_are_groupoids
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    ∀ U : C,
      IsGroupoid (Functor.Fiber
        (canonicalFibredTwoFibreProduct X Y S F G).diagram.base U) := by
  intro U
  obtain ⟨e⟩ := twoFibreProductOver_fibre_equivalent
    F.underlying G.underlying U
  let _ : IsGroupoid
      (IsoComma (overMorphismFiberFunctor F.underlying U)
        (overMorphismFiberFunctor G.underlying U)) := by
    constructor
    intro a b f
    let _ : IsIso f.hom.left := (hX U).all_isIso _
    let _ : IsIso f.hom.right := (hY U).all_isIso _
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
  let _ : e.functor.IsEquivalence := by infer_instance
  refine { all_isIso := ?_ }
  intro a b f
  let _ : IsIso (e.functor.map f) :=
    (inferInstance : IsGroupoid
      (IsoComma (overMorphismFiberFunctor F.underlying U)
        (overMorphismFiberFunctor G.underlying U))).all_isIso _
  exact e.fullyFaithfulFunctor.isIso_of_isIso_map f

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

/- Proof roadmap: choose a quasi-inverse to the underlying equivalence, lift
it to a functor strictly over `C` by cartesian transport, prove that it
preserves cartesian arrows, and lift the unit and counit to vertical natural
isomorphisms.  Package the result as `IsEquivalenceOverHom`.  The blocked step
is strictifying the quasi-inverse and both isomorphisms over the base. -/
theorem equivalence_fibredInGroupoids_is_equivalence_over
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y)
    (hF : Nonempty (overFunctor F.underlying).IsEquivalence) :
    IsEquivalenceOverHom F := by
  sorry

/- Proof roadmap: use the iso-comma description of the 2-fibre product.  In
one direction, full faithfulness gives the unique source isomorphism lifting
the comparison isomorphism, hence essential surjectivity and full
faithfulness of the diagonal.  Conversely, apply a quasi-inverse of the
diagonal to comparison isomorphisms to recover bijectivity on homs.  Transfer
the result back through `twoFibreProductOverCategory_canonically_equivalent`.
-/
theorem fibredInGroupoids_fullyFaithful_iff_diagonal_isEquivalence
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (F : FibredCategoryOverHom X Y) :
      Nonempty (overFunctor F.underlying).FullyFaithful ↔
      (fibredCategoryDiagonalFunctor F).IsEquivalence := by
  constructor
  · rintro ⟨hH⟩
    let H := overFunctor F.underlying
    let D := fibredCategoryDiagonalFunctor F
    let _ : H.FullyFaithful := hH
    let preimage {x y : X.underlying.left}
        (f : D.obj x ⟶ D.obj y) : x ⟶ y :=
      f.hom.hom.left
    have hmap_preimage {x y : X.underlying.left}
        (f : D.obj x ⟶ D.obj y) :
        D.map (preimage f) = f := by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · rfl
      · apply hH.map_injective
        have hw : H.map f.hom.hom.left = H.map f.hom.hom.right := by
          simpa [D, fibredCategoryDiagonalFunctor, isoCommaDiagonal]
            using f.hom.hom.w
        exact hw
    have hDff : D.FullyFaithful :=
      Functor.FullyFaithful.mk preimage
        (by intro x y f; exact hmap_preimage f)
        (by intro x y f; rfl)
    exact ⟨hDff.faithful, hDff.full, by
      constructor
      intro z
      let f : z.obj.obj.left ⟶ z.obj.obj.right :=
        hH.preimage z.obj.obj.hom
      let : IsIso (H.map f) := by
        dsimp [f]
        rw [hH.map_preimage]
        exact z.obj.property
      let _ : IsIso f := hH.isIso_of_isIso_map f
      refine ⟨z.obj.obj.left, ⟨ObjectProperty.isoMk _
        (ObjectProperty.isoMk _
          (Comma.isoMk (Iso.refl _)
            (@asIso _ _ _ _ f (hH.isIso_of_isIso_map f)) ?_))⟩⟩
      dsimp [D, fibredCategoryDiagonalFunctor, isoCommaDiagonal,
        ObjectProperty.isoMk, Comma.isoMk]
      simp [f, hH.map_preimage]
      ⟩
  · intro hD
    let pX := structureFunctor X.underlying
    let pY := structureFunctor Y.underlying
    let pT := twoFibreProductOverBaseFunctor F.underlying F.underlying
    let D := fibredCategoryDiagonalFunctor F
    let _ : pX.IsFibredInGroupoids :=
      groupoidFibredCategoryOver_isFibredInGroupoids X hX
    let _ : pY.IsFibredInGroupoids :=
      groupoidFibredCategoryOver_isFibredInGroupoids Y hY
    let P : FibredInGroupoidsTwoFibreProduct.{v, u, u, v} F F := {
      product := canonicalFibredTwoFibreProduct X X Y F F
      fibres_are_groupoids :=
        canonicalFibredTwoFibreProduct_fibres_are_groupoids.{v, u, u, v}
          X X Y hX hX F F }
    have hpT : pT.IsFibredInGroupoids := by
      have hbase :
          (canonicalFibredTwoFibreProduct.{v, u, u, v} X X Y F F).diagram.base =
            pT := by
        rw [canonicalFibredTwoFibreProduct_diagram]
        rfl
      rw [← hbase]
      exact fibredInGroupoidsTwoFibreProduct_apex_isFibredInGroupoids P
    have hDfibre : ∀ U : C,
        (fibreFunctor pX pT D rfl U).IsEquivalence := by
      intro U
      exact (fibredInGroupoids_equivalence_iff_fibrewise
        pX pT D rfl (groupoidFibredCategoryOver_isFibredInGroupoids X hX)
          hpT).mp hD U
    apply (fibredInGroupoids_fullyFaithful_iff_fibrewise
      pX pY (overFunctor F.underlying) (overFunctor_comm F.underlying)
      (groupoidFibredCategoryOver_isFibredInGroupoids X hX)
      (groupoidFibredCategoryOver_isFibredInGroupoids Y hY)).mpr
    intro U
    let G := fibreFunctor pX pY (overFunctor F.underlying)
      (overFunctor_comm F.underlying) U
    let dU := fibreFunctor pX pT D rfl U
    let _ : dU.IsEquivalence := hDfibre U
    let hDff : dU.FullyFaithful :=
      Functor.FullyFaithful.ofFullyFaithful dU
    let hDfull : dU.Full := hDff.full
    let hDess : dU.EssSurj := inferInstance
    have hGfull : G.Full := by
      constructor
      intro x y f
      let _ : IsIso f.1 := by
        change IsIso (Functor.Fiber.fiberInclusion.map f)
        let _ : IsIso f := (hY U).all_isIso f
        exact (Functor.Fiber.fiberInclusion.mapIso (asIso f)).isIso_hom
      let zobj : TwoFibreProductOverCategory F.underlying F.underlying :=
        { obj :=
            { obj := { left := x.1, right := y.1, hom := f.1 }
              property := by
                change IsIso f.1
                infer_instance }
          property := ⟨U, x.2, y.2, f.2⟩ }
      let z : Functor.Fiber pT U := ⟨zobj, by
        change pX.obj x.1 = U
        exact x.2⟩
      obtain ⟨w, ⟨e⟩⟩ := hDess.mem_essImage z
      let a : x.1 ⟶ w.1 := e.inv.1.hom.hom.left
      let b : y.1 ⟶ w.1 := e.inv.1.hom.hom.right
      have ha : pX.IsHomLift (𝟙 U) a := by
        apply CategoryTheory.IsHomLift.of_fac' pX (𝟙 U) a x.2 w.2
        let _ : pT.IsHomLift (𝟙 U) e.inv.1 := e.inv.2
        have hefac := CategoryTheory.IsHomLift.fac' pT (𝟙 U) e.inv.1
        dsimp [pT, twoFibreProductOverBaseFunctor,
          twoFibreProductOverLeft, TwoFibreProductOverProperty,
          isoCommaLeft] at hefac
        exact hefac
      have hb : pX.IsHomLift (𝟙 U) b := by
        apply CategoryTheory.IsHomLift.of_fac' pX (𝟙 U) b y.2 w.2
        let _ : pX.IsHomLift (𝟙 U) a := ha
        have hfacA := CategoryTheory.IsHomLift.fac' pX (𝟙 U) a
        obtain ⟨U', U'', hx, hy, hx', hy', hbase⟩ :=
          twoFibreProductOver_morphism_base_description e.inv.1
        change eqToHom hx.symm ≫ pX.map a ≫ eqToHom hx' =
          eqToHom hy.symm ≫ pX.map b ≫ eqToHom hy' at hbase
        have hU' : U' = U := hx.symm.trans x.2
        have hU'' : U'' = U := hx'.symm.trans w.2
        cases hU'
        cases hU''
        dsimp [z, zobj] at hx hy
        dsimp [dU, fibreFunctor, D, fibredCategoryDiagonalFunctor,
          isoCommaDiagonal] at hx' hy' hbase
        change pX.obj x.1 = U at hx
        change pX.obj y.1 = U at hy
        change pX.obj w.1 = U at hx'
        change pX.obj w.1 = U at hy'
        have hx0 : hx = x.2 := Subsingleton.elim _ _
        have hy0 : hy = y.2 := Subsingleton.elim _ _
        have hx'0 : hx' = w.2 := Subsingleton.elim _ _
        have hy'0 : hy' = w.2 := Subsingleton.elim _ _
        rw [hx0, hy0, hx'0, hy'0, hfacA] at hbase
        have hbase' := congrArg
          (fun q => eqToHom y.2 ≫ q ≫ eqToHom w.2.symm) hbase
        simpa [a, b, Category.assoc, eqToHom_trans] using hbase'.symm
      let a₀ : x ⟶ w := ⟨a, ha⟩
      let b₀ : y ⟶ w := ⟨b, hb⟩
      let _ : IsIso b₀ := (hX U).all_isIso b₀
      let _ : IsIso (G.map b₀) := by infer_instance
      let _ : IsIso b := by
        change IsIso (Functor.Fiber.fiberInclusion.map b₀)
        exact (Functor.Fiber.fiberInclusion.mapIso (asIso b₀)).isIso_hom
      let hcomm : (overFunctor F.underlying).map a =
          f.1 ≫ (overFunctor F.underlying).map b := by
        have hw := e.inv.1.hom.hom.w
        dsimp [z, zobj, dU, fibreFunctor, D,
          fibredCategoryDiagonalFunctor, isoCommaDiagonal] at hw
        rw [Category.comp_id] at hw
        change (overFunctor F.underlying).map a =
          f.1 ≫ (overFunctor F.underlying).map b at hw
        exact hw
      have hcommG : G.map a₀ = f ≫ G.map b₀ := by
        apply Functor.Fiber.hom_ext
        change (overFunctor F.underlying).map a =
          f.1 ≫ (overFunctor F.underlying).map b
        exact hcomm
      refine ⟨a₀ ≫ inv b₀, ?_⟩
      rw [Functor.map_comp, hcommG]
      simp
    have hGfaithful : G.Faithful := by
      constructor
      intro x y f g hfg
      have hfg' : (overFunctor F.underlying).map f.1 =
          (overFunctor F.underlying).map g.1 := by
        exact congrArg (fun k => k.1) hfg
      let η₀ : (dU.obj x).1 ⟶ (dU.obj y).1 := by
        apply ObjectProperty.homMk
        apply ObjectProperty.homMk
        refine { left := f.1, right := g.1, w := ?_ }
        change (overFunctor F.underlying).map f.1 ≫ 𝟙 _ =
          𝟙 _ ≫ (overFunctor F.underlying).map g.1
        simp [hfg']
      let η : dU.obj x ⟶ dU.obj y := by
        refine ⟨η₀, ?_⟩
        let _ : pX.IsHomLift (𝟙 U) f.1 := f.2
        apply CategoryTheory.IsHomLift.of_fac' pT (𝟙 U) η₀
          (dU.obj x).2 (dU.obj y).2
        have hfac := CategoryTheory.IsHomLift.fac' pX (𝟙 U) f.1
        change pX.map f.1 =
          eqToHom ((dU.obj x).2) ≫ 𝟙 U ≫
            eqToHom ((dU.obj y).2).symm
        have hxproof : (dU.obj x).2 = x.2 := Subsingleton.elim _ _
        have hyproof : (dU.obj y).2 = y.2 := Subsingleton.elim _ _
        rw [hxproof, hyproof]
        exact hfac
      obtain ⟨h, hh⟩ := hDfull.map_surjective η
      have hleft := congrArg (fun k => k.1.hom.hom.left) hh
      have hright := congrArg (fun k => k.1.hom.hom.right) hh
      apply Functor.Fiber.hom_ext
      change f.1 = g.1
      have hleft' : h.1 = f.1 := by
        simpa [η, η₀, dU, fibreFunctor, D, fibredCategoryDiagonalFunctor,
          isoCommaDiagonal] using hleft
      have hright' : h.1 = g.1 := by
        simpa [η, η₀, dU, fibreFunctor, D, fibredCategoryDiagonalFunctor,
          isoCommaDiagonal] using hright
      exact hleft'.symm.trans hright'
    exact ⟨Functor.FullyFaithful.mk
      (fun {x y} f => Classical.choose (hGfull.map_surjective f))
      (by intro x y f; exact Classical.choose_spec (hGfull.map_surjective f))
      (by intro x y f; apply hGfaithful.map_injective
          exact Classical.choose_spec (hGfull.map_surjective _))⟩

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
        fibredOverNatTransComp (fibredWhiskerRight η ψ)
          (fibredWhiskerRight θ ψ) by
      apply OverNatTrans.ext
      exact congrArg (fun q => q.toNatTrans)
        (Bicategory.comp_whiskerRight (B := FibredCategoryOver C)
          η θ ψ)]
    rfl

/- Proof roadmap: strictify the two supplied equivalences over `C` with
`equivalence_fibredInGroupoids_is_equivalence_over`; define the quasi-inverse
of `prePostcompositionFunctor` by pre- and postcomposing with the chosen
inverse fibred homs; then build its unit and counit by whiskering the four
vertical isomorphisms and discharge coherence using bicategory associators.
-/
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
    (prePostcompositionFunctor φ ψ).IsEquivalence := by sorry
  /-
  obtain ⟨φi, ⟨eφL⟩, ⟨eφR⟩⟩ :=
    equivalence_fibredInGroupoids_is_equivalence_over hX₁ hX₂ φ hφ
  obtain ⟨ψi, ⟨eψL⟩, ⟨eψR⟩⟩ :=
    equivalence_fibredInGroupoids_is_equivalence_over hX₃ hX₄ ψ hψ
  let Q : FibredCategoryOverHom X₁ X₄ ⥤
      FibredCategoryOverHom X₂ X₃ := {
    obj := fun α => FibredCategoryOverHom.comp φi
      (FibredCategoryOverHom.comp α ψi)
    map := fun η => fibredWhiskerLeft φi (fibredWhiskerRight η ψi)
    map_id := by
      intro α
      rw [show fibredWhiskerRight (𝟙 α) ψi =
          𝟙 (FibredCategoryOverHom.comp α ψi) by
        exact @Bicategory.id_whiskerRight (FibredCategoryOver C) _
          X₁ X₄ X₃ α ψi]
      exact @Bicategory.whiskerLeft_id (FibredCategoryOver C) _
        X₂ X₁ X₃ φi (FibredCategoryOverHom.comp α ψi)
    map_comp := by
      intro α β γ η θ
      apply OverNatTrans.ext
      change
        (fibredWhiskerLeft φi (fibredWhiskerRight (η ≫ θ) ψi)).toNatTrans =
          (fibredWhiskerLeft φi (fibredWhiskerRight η ψi)).toNatTrans ≫
            (fibredWhiskerLeft φi (fibredWhiskerRight θ ψi)).toNatTrans
      rw [show fibredWhiskerRight (η ≫ θ) ψi =
          fibredOverNatTransComp (fibredWhiskerRight η ψi)
            (fibredWhiskerRight θ ψi) by
        apply OverNatTrans.ext
        exact congrArg (fun q => q.toNatTrans)
          (Bicategory.comp_whiskerRight (B := FibredCategoryOver C)
            η θ ψi)]
      rfl }
  let toHomIso {U V : FibredCategoryOver C}
      {F G : FibredCategoryOverHom U V}
      (e : @Iso _ (Bicategory.homCategory (B := FibredCategoryOver C) U V)
        F G) : F ≅ G := {
    hom := e.hom
    inv := e.inv
    hom_inv_id := by
      apply OverNatTrans.ext
      exact congrArg (fun q => q.toNatTrans) e.hom_inv_id
    inv_hom_id := by
      apply OverNatTrans.ext
      exact congrArg (fun q => q.toNatTrans) e.inv_hom_id }
  let P := prePostcompositionFunctor φ ψ
  let unitComponent (α : FibredCategoryOverHom X₂ X₃) :
      α ≅ (P ⋙ Q).obj α := by
    change α ≅ FibredCategoryOverHom.comp φi
      (FibredCategoryOverHom.comp
        (FibredCategoryOverHom.comp φ
          (FibredCategoryOverHom.comp α ψ)) ψi)
    let lastB := Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φi
      ((Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φ
          (Bicategory.associator (B := FibredCategoryOver C)
            α ψ ψi).symm) ≪≫
        (Bicategory.associator (B := FibredCategoryOver C)
          φ (FibredCategoryOverHom.comp α ψ) ψi).symm)
    let last := toHomIso lastB
    let preB :=
        ((Bicategory.leftUnitor (B := FibredCategoryOver C) α).symm ≪≫
          Bicategory.whiskerLeftIso (B := FibredCategoryOver C)
            (FibredCategoryOverHom.id X₂)
            (Bicategory.rightUnitor (B := FibredCategoryOver C) α).symm) ≪≫
        Bicategory.whiskerRightIso (B := FibredCategoryOver C) eφR.symm
          (FibredCategoryOverHom.comp α (FibredCategoryOverHom.id X₃)) ≪≫
        Bicategory.associator (B := FibredCategoryOver C) φi φ
          (FibredCategoryOverHom.comp α (FibredCategoryOverHom.id X₃)) ≪≫
        Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φi
          (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φ
            (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) α
              eψL.symm))
    let pre :
        α ≅ FibredCategoryOverHom.comp φi
          (FibredCategoryOverHom.comp φ
            (FibredCategoryOverHom.comp α
              (FibredCategoryOverHom.comp ψ ψi))) := by
      convert toHomIso preB using 1 <;>
        apply FibredCategoryOverHom.ext <;> rfl
    convert pre ≪≫ last using 1 <;>
      apply FibredCategoryOverHom.ext <;> rfl
  let unit : 𝟭 (FibredCategoryOverHom X₂ X₃) ≅ P ⋙ Q :=
    NatIso.ofComponents unitComponent (by
      intro α β η
      dsimp [unitComponent, P, Q, prePostcompositionFunctor, toHomIso]
      sorry
      /- simp [fibredWhiskerLeft, fibredWhiskerRight,
        fibredOverNatTransComp, fibredCategoryOverHomCategory,
        overWhiskerLeft, overWhiskerRight,
        overHomCategory, fibredHomIsoOfUnderlying,
        overNatIsoOfUnderlying, Functor.whiskerLeft,
        Functor.whiskerRight, Functor.comp, Category.assoc,
        NatTrans.comp_app, Bicategory.Strict.assoc,
        Bicategory.Strict.id_comp, Bicategory.Strict.comp_id]) -/)
  let counitComponent (β : FibredCategoryOverHom X₁ X₄) :
      β ≅ (Q ⋙ P).obj β := by
    change β ≅ FibredCategoryOverHom.comp φ
      (FibredCategoryOverHom.comp
        (FibredCategoryOverHom.comp φi
          (FibredCategoryOverHom.comp β ψi)) ψ)
    let preB :=
        ((Bicategory.leftUnitor (B := FibredCategoryOver C) β).symm ≪≫
          Bicategory.whiskerLeftIso (B := FibredCategoryOver C)
            (FibredCategoryOverHom.id X₁)
            (Bicategory.rightUnitor (B := FibredCategoryOver C) β).symm) ≪≫
        Bicategory.whiskerRightIso (B := FibredCategoryOver C) eφL.symm
          (FibredCategoryOverHom.comp β (FibredCategoryOverHom.id X₄)) ≪≫
        Bicategory.associator (B := FibredCategoryOver C) φ φi
          (FibredCategoryOverHom.comp β (FibredCategoryOverHom.id X₄)) ≪≫
        Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φ
          (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φi
            (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) β
              eψR.symm))
    let lastB := Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φ
      ((Bicategory.whiskerLeftIso (B := FibredCategoryOver C) φi
          (Bicategory.associator (B := FibredCategoryOver C)
            β ψi ψ).symm) ≪≫
        (Bicategory.associator (B := FibredCategoryOver C)
          φi (FibredCategoryOverHom.comp β ψi) ψ).symm)
    let pre := toHomIso preB
    let last := toHomIso lastB
    convert pre ≪≫ last using 1 <;>
      apply FibredCategoryOverHom.ext <;> rfl
  let counit : Q ⋙ P ≅ 𝟭 (FibredCategoryOverHom X₁ X₄) :=
    NatIso.ofComponents (fun β => (counitComponent β).symm) (by
      intro α β η
      have hforward : η ≫ (counitComponent β).hom =
          (counitComponent α).hom ≫ (Q ⋙ P).map η := by
        apply OverNatTrans.ext
        dsimp [counitComponent, P, Q, prePostcompositionFunctor, toHomIso]
        sorry
        /- simp [fibredWhiskerLeft, fibredWhiskerRight,
          fibredOverNatTransComp, fibredCategoryOverHomCategory,
          overWhiskerLeft, overWhiskerRight,
          overHomCategory, fibredHomIsoOfUnderlying,
          overNatIsoOfUnderlying, Functor.whiskerLeft,
          Functor.whiskerRight, Functor.comp, Category.assoc,
          NatTrans.comp_app, Bicategory.Strict.assoc,
        Bicategory.Strict.id_comp, Bicategory.Strict.comp_id] -/)
      apply (cancel_mono (counitComponent β).hom).1
      simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Functor.id_map, Category.comp_id]
      rw [hforward]
      simp)
  exact Functor.IsEquivalence.mk' Q unit counit
  -/

/-! ## Inertia, slices, composites, and fibre products -/

theorem inertia_isFibredInGroupoids
    {C : Cat.{v, u}} (X : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X) :
    (relativeInertiaBase (toBaseFibredHom X).underlying).IsFibredInGroupoids := by
  let p := relativeInertiaBase (toBaseFibredHom X).underlying
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres p).mpr
  constructor
  · intro U
    let hgroup : IsGroupoid
        (Functor.Fiber (structureFunctor X.underlying) U) := hX U
    constructor
    intro A B f
    let _ : p.IsHomLift (𝟙 U) f.1 := f.2
    let hA : (structureFunctor X.underlying).obj A.1.carrier = U := by
      simpa [p, relativeInertiaBase, relativeInertiaStructureMap] using A.2
    let hB : (structureFunctor X.underlying).obj B.1.carrier = U := by
      simpa [p, relativeInertiaBase, relativeInertiaStructureMap] using B.2
    have hfibre : (structureFunctor X.underlying).IsHomLift
        (𝟙 U) f.1.hom := by
      apply CategoryTheory.IsHomLift.of_fac'
        (structureFunctor X.underlying) (𝟙 U) f.1.hom hA hB
      have hfac := CategoryTheory.IsHomLift.fac' p (𝟙 U) f.1
      dsimp [p, relativeInertiaBase, relativeInertiaStructureMap] at hfac
      exact hfac
    let _ : (structureFunctor X.underlying).IsHomLift
        (𝟙 U) f.1.hom := hfibre
    let k := Functor.Fiber.homMk (structureFunctor X.underlying) U f.1.hom
    let _ : IsIso k := hgroup.all_isIso k
    let _ : IsIso f.1.hom := by
      change IsIso (Functor.Fiber.fiberInclusion.map k)
      exact (Functor.Fiber.fiberInclusion.mapIso (asIso k)).isIso_hom
    let g : B.1 ⟶ A.1 :=
      { hom := inv f.1.hom
        comm := by
          apply (cancel_mono f.1.hom).1
          simp [Category.assoc, f.1.comm] }
    let _ : IsIso (p.map f.1) := by
      dsimp [p, relativeInertiaBase, relativeInertiaStructureMap]
      infer_instance
    have hg : p.IsHomLift (𝟙 U) g := by
      apply CategoryTheory.IsHomLift.of_fac' p (𝟙 U) g B.2 A.2
      have hfac := CategoryTheory.IsHomLift.fac' p (𝟙 U) f.1
      have hg_inv : p.map g = inv (p.map f.1) := by
        apply IsIso.eq_inv_of_hom_inv_id
        simp [g, p, relativeInertiaBase, relativeInertiaStructureMap]
      calc
        p.map g = inv (p.map f.1) := hg_inv
        _ = eqToHom B.2 ≫ 𝟙 U ≫ eqToHom A.2.symm := by
          symm
          apply IsIso.eq_inv_of_hom_inv_id
          rw [hfac]
          simp
    let gi : B ⟶ A := ⟨g, hg⟩
    refine ⟨⟨gi, ?_, ?_⟩⟩
    · apply Functor.Fiber.hom_ext
      apply RelativeInertiaHom.ext
      change f.1.hom ≫ inv f.1.hom = 𝟙 A.1.carrier
      simp
    · apply Functor.Fiber.hom_ext
      apply RelativeInertiaHom.ext
      change inv f.1.hom ≫ f.1.hom = 𝟙 B.1.carrier
      simp
  · let _ : (structureFunctor X.underlying).IsFibredInGroupoids :=
      groupoidFibredCategoryOver_isFibredInGroupoids X hX
    exact relativeInertia_isFibred (toBaseFibredHom X)

theorem fibredInGroupoids_over_slice
    {S C : Type*} [Category* S] [Category* C]
    (U : C) (p : S ⥤ C) (p' : S ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p)
    (hp : p.IsFibredInGroupoids) :
    p'.IsFibredInGroupoids := by
  let q := p' ⋙ Over.forget U
  have hq : q.IsFibredInGroupoids := by
    dsimp [q]
    rw [factor]
    exact hp
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres p').mpr
  constructor
  · intro R
    let hgroup : IsGroupoid (Functor.Fiber q R.left) :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 R.left
    constructor
    intro X Y f
    let _ : p'.IsHomLift (𝟙 R) f.1 := f.2
    let hX : q.obj X.1 = R.left := by
      simpa [q] using congrArg (fun T : Over U => T.left) X.2
    let hY : q.obj Y.1 = R.left := by
      simpa [q] using congrArg (fun T : Over U => T.left) Y.2
    have hpf : q.IsHomLift (𝟙 R.left) f.1 := by
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 R.left) f.1 hX hY
      change (p'.map f.1).left = _
      have h := CategoryTheory.IsHomLift.fac' p' (𝟙 R) f.1
      have h' := congrArg (fun k => k.left) h
      simpa [Over.eqToHom_left, q, Category.assoc, ← eqToHom_trans] using h'
    let _ : q.IsHomLift (𝟙 R.left) f.1 := hpf
    let k := Functor.Fiber.homMk q R.left f.1
    let _ : IsIso k := hgroup.all_isIso k
    let _ : IsIso f.1 := by
      change IsIso (Functor.Fiber.fiberInclusion.map k)
      exact (Functor.Fiber.fiberInclusion.mapIso (asIso k)).isIso_hom
    let _ : p'.IsHomLift (𝟙 R) (inv f.1) :=
      CategoryTheory.IsHomLift.lift_id_inv_isIso p' R f.1
    let g : Y ⟶ X := ⟨inv f.1, inferInstance⟩
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply Functor.Fiber.hom_ext
      change f.1 ≫ inv f.1 = 𝟙 X.1
      simp
    · apply Functor.Fiber.hom_ext
      change inv f.1 ≫ f.1 = 𝟙 Y.1
      simp
  · let _ : p.IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.2
    exact fibred_over_slice U p p' factor

theorem fibredInGroupoids_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C)
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids) :
    (p ⋙ q).IsFibredInGroupoids := by
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres (p ⋙ q)).mpr
  constructor
  · intro U
    let hqgroup : IsGroupoid (Functor.Fiber q U) :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.1 U
    constructor
    intro X Y f
    let _ : (p ⋙ q).IsHomLift (𝟙 U) f.1 := f.2
    have hqf : q.IsHomLift (𝟙 U) (p.map f.1) := by
      let hdom := CategoryTheory.IsHomLift.domain_eq (p ⋙ q) (𝟙 U) f.1
      let hcod := CategoryTheory.IsHomLift.codomain_eq (p ⋙ q) (𝟙 U) f.1
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 U) (p.map f.1)
        hdom hcod
      have hfac := CategoryTheory.IsHomLift.fac' (p ⋙ q) (𝟙 U) f.1
      simpa only [Functor.comp_map] using hfac
    let _ : q.IsHomLift (𝟙 U) (p.map f.1) := hqf
    let k := Functor.Fiber.homMk q U (p.map f.1)
    let _ : IsIso k := hqgroup.all_isIso k
    let _ : IsIso (p.map f.1) := by
      change IsIso (Functor.Fiber.fiberInclusion.map k)
      exact (Functor.Fiber.fiberInclusion.mapIso (asIso k)).isIso_hom
    let _ : p.IsStronglyCartesian (p.map f.1) f.1 :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p hp f.1
    let _ : IsIso f.1 :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map f.1) f.1
    let _ : (p ⋙ q).IsHomLift (𝟙 U) (inv f.1) :=
      CategoryTheory.IsHomLift.lift_id_inv_isIso (p := p ⋙ q) U f.1
    let g : Y ⟶ X := ⟨inv f.1, inferInstance⟩
    refine ⟨⟨g, ?_, ?_⟩⟩
    · apply Functor.Fiber.hom_ext
      change f.1 ≫ inv f.1 = 𝟙 X.1
      simp
    · apply Functor.Fiber.hom_ext
      change inv f.1 ≫ f.1 = 𝟙 Y.1
      simp
  · let _ : p.IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres p).mp hp |>.2
    let _ : q.IsFibered :=
      (fibredInGroupoids_iff_fibred_groupoid_fibres q).mp hq |>.2
    exact fibred_over_fibred p q

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

/-- Forgetting the equations and verticality data from an equivalence over a
base gives an ordinary equivalence of the total categories. -/
theorem isEquivalence_of_isEquivalenceOverFunctor
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (p : Functor A D) (q : Functor B D) (h : Functor A B)
    (hh : IsEquivalenceOverFunctor p q h) : h.IsEquivalence := by
  rcases hh with ⟨k, _hk, _hh, ⟨unit, _unitOver, _hunit⟩,
    ⟨counit, _counitOver, _hcounit⟩⟩
  exact Functor.IsEquivalence.mk' k unit.symm counit

/-- A fully faithful functor over the base reflects strongly Cartesian
arrows.  This formulation is universe-polymorphic and does not require the
two total categories to live in the same universe. -/
theorem isStronglyCartesian_of_map_fullyFaithful
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (p : Functor A D) (q : Functor B D) (F : Functor A B)
    (over : F ⋙ q = p) [F.Full] [F.Faithful]
    {x y : A} (f : x ⟶ y)
    (hf : q.IsStronglyCartesian (q.map (F.map f)) (F.map f)) :
    p.IsStronglyCartesian (p.map f) f := by
  let _ : q.IsStronglyCartesian (q.map (F.map f)) (F.map f) := hf
  constructor
  intro z g k hk
  let hx : q.obj (F.obj x) = p.obj x := Functor.congr_obj over x
  let hy : q.obj (F.obj y) = p.obj y := Functor.congr_obj over y
  let hz : q.obj (F.obj z) = p.obj z := Functor.congr_obj over z
  let g' : q.obj (F.obj z) ⟶ q.obj (F.obj x) :=
    eqToHom hz ≫ g ≫ eqToHom hx.symm
  have hFf : q.map (F.map f) =
      eqToHom hx ≫ p.map f ≫ eqToHom hy.symm :=
    Functor.congr_hom over f
  have hFk : q.map (F.map k) =
      eqToHom hz ≫ p.map k ≫ eqToHom hy.symm :=
    Functor.congr_hom over k
  have hkmap : p.map k = g ≫ p.map f :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift p (g ≫ p.map f) k).symm
  have hfactor : q.map (F.map k) = g' ≫ q.map (F.map f) := by
    rw [hFk, hFf, hkmap]
    dsimp [g']
    simp [Category.assoc]
  let _ : q.IsHomLift (q.map (F.map k)) (F.map k) := Functor.IsHomLift.map _
  obtain ⟨l', ⟨hl', hl'comp⟩, hl'unique⟩ :=
    Functor.IsStronglyCartesian.universal_property q
      (q.map (F.map f)) (F.map f) g' (q.map (F.map k)) hfactor (F.map k)
  obtain ⟨l, hl⟩ := F.map_surjective l'
  have hlmap : p.map l = g := by
    have hFl : q.map (F.map l) =
        eqToHom hz ≫ p.map l ≫ eqToHom hx.symm :=
      Functor.congr_hom over l
    have hlift : q.map l' = g' :=
      (CategoryTheory.IsHomLift.eq_of_isHomLift q g' l').symm
    apply (cancel_epi (eqToHom hz)).1
    apply (cancel_mono (eqToHom hx.symm)).1
    calc
      (eqToHom hz ≫ p.map l) ≫ eqToHom hx.symm =
          q.map (F.map l) := by
            simpa only [Category.assoc] using hFl.symm
      _ = q.map l' := by rw [hl]
      _ = g' := hlift
      _ = (eqToHom hz ≫ g) ≫ eqToHom hx.symm := by
        dsimp [g']
        simp only [Category.assoc]
  have hlift : p.IsHomLift g l := by
    apply CategoryTheory.IsHomLift.of_fac' p g l rfl rfl
    simpa using hlmap
  refine ⟨l, ⟨hlift, ?_⟩, ?_⟩
  · apply F.map_injective
    simpa [Functor.map_comp, hl] using hl'comp
  · intro m hm
    apply F.map_injective
    rw [hl]
    apply hl'unique (F.map m)
    constructor
    · let _ : p.IsHomLift g m := hm.1
      have hFm : q.map (F.map m) =
          eqToHom hz ≫ p.map m ≫ eqToHom hx.symm :=
        Functor.congr_hom over m
      have hmmap : p.map m = g :=
        (CategoryTheory.IsHomLift.eq_of_isHomLift p g m).symm
      have hFmlift : q.map (F.map m) = g' := by
        rw [hFm, hmmap]
      apply CategoryTheory.IsHomLift.of_fac' q g' (F.map m) rfl rfl
      simpa using hFmlift
    · simpa [Functor.map_comp, hl] using congrArg F.map hm.2

/-- An equivalence over a common base transports the fibred-in-groupoids
structure, and induces an equivalence on every fibre.  In particular, the
last conjunct packages the fibre functor's full-faithfulness and essential
surjectivity needed when comparing fibre objects. -/
theorem fibredInGroupoids_of_isEquivalenceOverFunctor
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hG : IsEquivalenceOverFunctor p p' G)
    (hp' : p'.IsFibredInGroupoids) :
      p.IsFibredInGroupoids ∧
      ∀ U : C, (fibreFunctor p p' G over U).IsEquivalence := by
  classical
  have hGeq : G.IsEquivalence :=
    isEquivalence_of_isEquivalenceOverFunctor p p' G hG
  let _ : G.IsEquivalence := hGeq
  let _ : G.Full := hGeq.full
  let _ : G.Faithful := hGeq.faithful
  rcases hG with ⟨K, hGK, hKp, ⟨unit, unitOver, hunit⟩,
    ⟨counit, counitOver, hcounit⟩⟩
  have hp : p.IsFibredInGroupoids := by
    constructor
    · intro V U f x hx
      have hx' : p'.obj (G.obj x) = U := by
        exact (congrArg (fun H : S ⥤ C => H.obj x) over).trans hx
      obtain ⟨y, φ, hφ⟩ := hp'.exists_lift f hx'
      let _ : p'.IsHomLift f φ := hφ
      let hy : p.obj (K.obj y) = V :=
        (congrArg (fun H : S' ⥤ C => H.obj y) hKp).trans
          (CategoryTheory.IsHomLift.domain_eq p' f φ)
      let χ : K.obj y ⟶ x := K.map φ ≫ unit.hom.app x
      refine ⟨K.obj y, χ, ?_⟩
      apply CategoryTheory.IsHomLift.of_fac' p f χ hy hx
      have hKφ := Functor.congr_hom hKp φ
      have hunit := hunit x
      have hφ' := CategoryTheory.IsHomLift.fac' p' f φ
      have hχbase : p.map χ =
          eqToHom hy ≫ f ≫ eqToHom hx.symm := by
        dsimp [χ]
        rw [Functor.map_comp, hunit]
        have hKφ' : p.map (K.map φ) =
            eqToHom (congrArg (fun H : S' ⥤ C => H.obj y) hKp) ≫
              p'.map φ ≫
                eqToHom (congrArg (fun H : S' ⥤ C => H.obj (G.obj x)) hKp).symm := by
          simpa only [Functor.comp_map] using hKφ
        rw [hKφ']
        rw [hφ']
        simp
      exact hχbase
    · intro x y z φ ψ f hcomp
      let hx : p'.obj (G.obj x) = p.obj x :=
        congrArg (fun H : S ⥤ C => H.obj x) over
      let hy : p'.obj (G.obj y) = p.obj y :=
        congrArg (fun H : S ⥤ C => H.obj y) over
      let hz : p'.obj (G.obj z) = p.obj z :=
        congrArg (fun H : S ⥤ C => H.obj z) over
      let f' : p'.obj (G.obj z) ⟶ p'.obj (G.obj y) :=
        eqToHom hz ≫ f ≫ eqToHom hy.symm
      have hbase : f' ≫ p'.map (G.map φ) = p'.map (G.map ψ) := by
        have hφ' := Functor.congr_hom over φ
        have hψ' := Functor.congr_hom over ψ
        have hφmap : p'.map (G.map φ) =
            eqToHom hy ≫ p.map φ ≫ eqToHom hx.symm := by
          simpa only [Functor.comp_map] using hφ'
        have hψmap : p'.map (G.map ψ) =
            eqToHom hz ≫ p.map ψ ≫ eqToHom hx.symm := by
          simpa only [Functor.comp_map] using hψ'
        rw [hφmap, hψmap]
        change (eqToHom hz ≫ f ≫ eqToHom hy.symm) ≫
            (eqToHom hy ≫ p.map φ ≫ eqToHom hx.symm) =
          eqToHom hz ≫ p.map ψ ≫ eqToHom hx.symm
        simp
        rw [← Category.assoc f (p.map φ) (eqToHom hx.symm)]
        rw [hcomp]
      obtain ⟨χ', hχ', hχunique⟩ := hp'.unique_lift (G.map φ) (G.map ψ) hbase
      obtain ⟨χ, hχmap⟩ := hGeq.full.map_surjective χ'
      refine ⟨χ, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · have hχmapbase : p.map χ = f := by
            have hχlift : p'.IsHomLift f' (G.map χ) := by
              rw [hχmap]
              exact hχ'.1
            let _ : p'.IsHomLift f' (G.map χ) := hχlift
            have hχ'base := CategoryTheory.IsHomLift.eq_of_isHomLift
              p' f' (G.map χ)
            have hχover := Functor.congr_hom over χ
            have hχover' : p'.map (G.map χ) =
                eqToHom hz ≫ p.map χ ≫ eqToHom hy.symm := by
              simpa only [Functor.comp_map] using hχover
            have hEq : eqToHom hz ≫ f ≫ eqToHom hy.symm =
                eqToHom hz ≫ p.map χ ≫ eqToHom hy.symm := by
              calc
                eqToHom hz ≫ f ≫ eqToHom hy.symm = f' := by rfl
                _ = p'.map (G.map χ) := hχ'base
                _ = eqToHom hz ≫ p.map χ ≫ eqToHom hy.symm := hχover'
            apply (cancel_epi (eqToHom hz)).1
            apply (cancel_mono (eqToHom hy.symm)).1
            simpa only [Category.assoc] using hEq.symm
          exact CategoryTheory.IsHomLift.of_fac' p f χ rfl rfl (by
          simpa using hχmapbase)
        · apply hGeq.faithful.map_injective
          rw [Functor.map_comp, hχmap]
          exact hχ'.2
      · intro χ₀ hχ₀
        have hχ₀map : G.map χ₀ = χ' := by
          let _ : p.IsHomLift f χ₀ := hχ₀.1
          have hχ₀base : p'.map (G.map χ₀) = f' := by
            have hχ₀p := CategoryTheory.IsHomLift.eq_of_isHomLift p f χ₀
            have hχ₀over := Functor.congr_hom over χ₀
            have hχ₀over' : p'.map (G.map χ₀) =
                eqToHom hz ≫ p.map χ₀ ≫ eqToHom hy.symm := by
              simpa only [Functor.comp_map] using hχ₀over
            dsimp [f']
            rw [hχ₀over', hχ₀p]
          have hχ₀lift : p'.IsHomLift f' (G.map χ₀) := by
            apply CategoryTheory.IsHomLift.of_fac' p' f' (G.map χ₀) rfl rfl
            simpa using hχ₀base
          have hχ₀comp : G.map χ₀ ≫ G.map φ = G.map ψ := by
            simpa only [Functor.map_comp] using congrArg G.map hχ₀.2
          exact hχunique (G.map χ₀) ⟨hχ₀lift, hχ₀comp⟩
        apply hGeq.faithful.map_injective
        exact hχ₀map.trans hχmap.symm
  refine ⟨hp, ?_⟩
  let _ : p.IsFibredInGroupoids := hp
  intro U
  have hp'group : IsGroupoid (Functor.Fiber p' U) :=
    (fibredInGroupoids_iff_fibred_groupoid_fibres p').mp hp' |>.1 U
  have hGff : Nonempty G.FullyFaithful :=
    ⟨Functor.FullyFaithful.ofFullyFaithful G⟩
  let hFiberFF : (fibreFunctor p p' G over U).FullyFaithful :=
    Classical.choice
      ((fibredInGroupoids_fullyFaithful_iff_fibrewise
        p p' G over hp hp').mp hGff U)
  let _ : (fibreFunctor p p' G over U).FullyFaithful := hFiberFF
  let _ : (fibreFunctor p p' G over U).Full := hFiberFF.full
  let _ : (fibreFunctor p p' G over U).Faithful := hFiberFF.faithful
  have hFiberEss : (fibreFunctor p p' G over U).EssSurj := by
    constructor
    intro y
    obtain ⟨x, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage G y.1
    let hx : p'.obj (G.obj x) = p.obj x :=
      congrArg (fun K : S ⥤ C => K.obj x) over
    let f : U ⟶ p.obj x :=
      eqToHom y.2.symm ≫ p'.map e.inv ≫ eqToHom hx
    let _ : IsIso f := by
      dsimp [f]
      infer_instance
    obtain ⟨x', φ, hφ⟩ := hp.exists_lift f rfl
    let _ : p.IsHomLift f φ := hφ
    have hdom : p.obj x' = U :=
      CategoryTheory.IsHomLift.domain_eq p f φ
    have hφmap : p.map φ = eqToHom hdom ≫ f := by
      simpa using CategoryTheory.IsHomLift.fac' p f φ
    let _ : IsIso (p.map φ) := by
      rw [hφmap]
      infer_instance
    let _ : p.IsStronglyCartesian (p.map φ) φ :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p hp φ
    let _ : IsIso φ :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ
    let hx' : p'.obj (G.obj x') = p.obj x' :=
      congrArg (fun K : S ⥤ C => K.obj x') over
    let hxU : p'.obj (G.obj x') = U := hx'.trans hdom
    let xU : Functor.Fiber p U := ⟨x', hdom⟩
    let k : (fibreFunctor p p' G over U).obj xU ⟶ y := by
      refine ⟨G.map φ ≫ e.hom, ?_⟩
      apply CategoryTheory.IsHomLift.of_fac' p' (𝟙 U)
        (G.map φ ≫ e.hom) hxU y.2
      have hGφ : p'.map (G.map φ) =
          eqToHom hx' ≫ p.map φ ≫ eqToHom hx.symm :=
        Functor.congr_hom over φ
      rw [Functor.map_comp, hGφ, hφmap]
      dsimp [f, hxU]
      simp [Category.assoc]
    let _ : IsIso k := hp'group.all_isIso k
    exact ⟨xU, ⟨asIso k⟩⟩
  exact {
    faithful := hFiberFF.faithful
    full := hFiberFF.full
    essSurj := hFiberEss }

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
  obtain ⟨U, hleft, hright, hhom⟩ :=
    groupoidAmelioration_object_description F ξ
  let _ : (structureFunctor Y.underlying).IsHomLift
      (𝟙 U) ξ.obj.hom := hhom
  let k := Functor.Fiber.homMk (structureFunctor Y.underlying) U ξ.obj.hom
  let _ : IsIso k := (hY U).all_isIso k
  change IsIso (Functor.Fiber.fiberInclusion.map k)
  exact (Functor.Fiber.fiberInclusion.mapIso (asIso k)).isIso_hom

/- Proof roadmap: start with Unit 33's `ameliorationFactorization`.  Use
`groupoidAmelioration_object_isIso` and the comma morphism equation to show
the middle projection has groupoid fibres; construct a quasi-inverse to
`data.u` from the canonical comma object and prove it is an equivalence over
`C`; finally prove `data.v` is fibred in groupoids by lifting arrows in `Y`
componentwise.  The remaining work is the over-base unit/counit bookkeeping.
-/
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

/- Proof roadmap: choose inverse fibred homs for `D.a` and `D.b`; compose them
to obtain the comparison `h`; use the two triangle 2-isomorphisms to identify
the composites over `Y`; prove `h` is an equivalence over `D.f` by composing
the chosen units and counits; and whisker those same isomorphisms to obtain
`D.b ≫ h ≅ D.a`.  A general composition/transport lemma for strict
equivalences over a base will make these steps routine. -/
theorem amelioration_unique
    {C : Cat.{v, u}} {X X' X'' Y : FibredCategoryOver C}
    {F : FibredCategoryOverHom X Y}
  (D : AmeliorationUniquenessData F) :
    ∃ h : FibredCategoryOverHom X'' X',
      IsEquivalenceOverFunctor (overFunctor D.g.underlying)
        (overFunctor D.f.underlying) (overFunctor h.underlying) ∧
      Nonempty (FibredCategoryOverHom.comp D.b h ≅ D.a) := by
  classical
  obtain ⟨bi, ⟨ebL⟩, ⟨ebR⟩⟩ := D.b_equivalence_over_C
  let h0 := FibredCategoryOverHom.comp bi D.a
  let eba : FibredCategoryOverHom.comp D.b h0 ≅ D.a :=
    (Bicategory.associator (B := FibredCategoryOver C) D.b bi D.a).symm ≪≫
      Bicategory.whiskerRightIso (B := FibredCategoryOver C) ebL D.a ≪≫
      Bicategory.leftUnitor (B := FibredCategoryOver C) D.a
  obtain ⟨φ, hφ⟩ := D.left_triangle
  obtain ⟨ψ, hψ⟩ := D.right_triangle
  let _ : IsIso φ := hφ
  let _ : IsIso ψ := hψ
  let eφ := asIso φ
  let eψ := asIso ψ
  let eF := eφ ≪≫ eψ.symm
  let eH :=
    Bicategory.associator (B := FibredCategoryOver C) bi D.a D.f ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) bi eF ≪≫
      (Bicategory.associator (B := FibredCategoryOver C) bi D.b D.g).symm ≪≫
      Bicategory.whiskerRightIso (B := FibredCategoryOver C) ebR D.g ≪≫
      Bicategory.leftUnitor (B := FibredCategoryOver C) D.g
  let eH' := underlyingIsoOfFibredHomIso eH
  let p := overFunctor D.f.underlying
  let q := overFunctor D.g.underlying
  let H := overFunctor h0.underlying
  change H ⋙ p ≅ q at eH'
  let hp := D.f_groupoid_fibred_over_Y
  let y (z : X''.underlying.left) :=
    Classical.choose (hp.exists_lift (eH'.inv.app z) rfl)
  let i (z : X''.underlying.left) : y z ⟶ H.obj z :=
    Classical.choose (Classical.choose_spec (hp.exists_lift (eH'.inv.app z) rfl))
  have hi (z : X''.underlying.left) :
      p.IsHomLift (eH'.inv.app z) (i z) :=
    Classical.choose_spec (Classical.choose_spec (hp.exists_lift (eH'.inv.app z) rfl))
  let hdom (z : X''.underlying.left) : p.obj (y z) = q.obj z := by
    let _ : p.IsHomLift (eH'.inv.app z) (i z) := hi z
    exact CategoryTheory.IsHomLift.domain_eq p (eH'.inv.app z) (i z)
  let basef {z₁ z₂ : X''.underlying.left} (f : z₁ ⟶ z₂) :
      p.obj (y z₁) ⟶ p.obj (y z₂) :=
    eqToHom (hdom z₁) ≫ q.map f ≫ eqToHom (hdom z₂).symm
  have hbase {z₁ z₂ : X''.underlying.left} (f : z₁ ⟶ z₂) :
      basef f ≫ p.map (i z₂) = p.map (i z₁ ≫ H.map f) := by
    let _ : p.IsHomLift (eH'.inv.app z₁) (i z₁) := hi z₁
    let _ : p.IsHomLift (eH'.inv.app z₂) (i z₂) := hi z₂
    rw [Functor.map_comp]
    rw [CategoryTheory.IsHomLift.fac' p (eH'.inv.app z₂) (i z₂)]
    rw [CategoryTheory.IsHomLift.fac' p (eH'.inv.app z₁) (i z₁)]
    simp [basef, Category.assoc]
  let m {z₁ z₂ : X''.underlying.left} (f : z₁ ⟶ z₂) : y z₁ ⟶ y z₂ :=
    Classical.choose ((hp.unique_lift (i z₂) (i z₁ ≫ H.map f) (hbase f)).exists)
  have hm {z₁ z₂ : X''.underlying.left} (f : z₁ ⟶ z₂) :
      p.IsHomLift (basef f) (m f) :=
    (Classical.choose_spec ((hp.unique_lift (i z₂) (i z₁ ≫ H.map f) (hbase f)).exists)).1
  have hmf {z₁ z₂ : X''.underlying.left} (f : z₁ ⟶ z₂) :
      m f ≫ i z₂ = i z₁ ≫ H.map f :=
    (Classical.choose_spec ((hp.unique_lift (i z₂) (i z₁ ≫ H.map f) (hbase f)).exists)).2
  let K : X''.underlying.left ⥤ X'.underlying.left := {
    obj := y
    map := m
    map_id := by
      intro z
      apply (hp.unique_lift (i z) (i z) (f := 𝟙 _) (by simp)).unique
      · refine ⟨?_, ?_⟩
        · simpa [basef] using hm (𝟙 z)
        · simpa using hmf (𝟙 z)
      · exact ⟨inferInstance, by simp⟩
    map_comp := by
      intro z₁ z₂ z₃ f g
      apply (hp.unique_lift (i z₃) (i z₁ ≫ H.map (f ≫ g))
        (f := basef (f ≫ g)) (hbase (f ≫ g))).unique
      · refine ⟨?_, ?_⟩
        · exact hm (f ≫ g)
        · exact hmf (f ≫ g)
      · let _ : p.IsHomLift (basef f) (m f) := hm f
        let _ : p.IsHomLift (basef g) (m g) := hm g
        have hcomp : p.IsHomLift (basef f ≫ basef g) (m f ≫ m g) := inferInstance
        refine ⟨?_, ?_⟩
        · simpa [basef, Category.assoc] using hcomp
        · rw [Category.assoc, hmf g, ← Category.assoc, hmf f, Category.assoc,
            ← Functor.map_comp]
  }
  have hKp : K ⋙ p = q := by
    refine CategoryTheory.Functor.ext (fun z => ?_) (fun z₁ z₂ f => ?_)
    · exact hdom z
    · let _ : p.IsHomLift (basef f) (m f) := hm f
      simpa [K, basef, Category.assoc] using
        (CategoryTheory.IsHomLift.fac' p (basef f) (m f))
  have hi_iso (z : X''.underlying.left) : IsIso (i z) := by
    let _ : p.IsHomLift (eH'.inv.app z) (i z) := hi z
    let _ : p.IsStronglyCartesian (p.map (i z)) (i z) :=
      fibredInGroupoids_all_morphisms_stronglyCartesian p hp (i z)
    let _ : IsIso (p.map (i z)) := by
      rw [CategoryTheory.IsHomLift.fac' p (eH'.inv.app z) (i z)]
      infer_instance
    exact stronglyCartesian_of_base_isIso p (p.map (i z)) (i z)
  let η : K ≅ H := NatIso.ofComponents (fun z => by
    let _ : IsIso (i z) := hi_iso z
    exact asIso (i z)) (by
      intro z₁ z₂ f
      exact hmf f)
  have hKbase :
      K ⋙ structureFunctor X'.underlying =
        structureFunctor X''.underlying := by
    calc
      K ⋙ structureFunctor X'.underlying =
          K ⋙ p ⋙ structureFunctor Y.underlying := by
            simpa only [Functor.assoc] using
              congrArg (fun R : X'.underlying.left ⥤ C =>
                K ⋙ R) (overFunctor_comm D.f.underlying).symm
      _ = q ⋙ structureFunctor Y.underlying := by
        simpa only [Functor.assoc] using
          congrArg (fun R : X''.underlying.left ⥤ Y.underlying.left =>
            R ⋙ structureFunctor Y.underlying) hKp
      _ = structureFunctor X''.underlying := overFunctor_comm D.g.underlying
  let Kover : CategoryOverHom X''.underlying X'.underlying :=
    ⟨Over.homMk (Cat.Hom.ofFunctor K)
      (by
        apply Cat.Hom.ext
        simpa only [Cat.Hom.toFunctor, Cat.Hom.comp_toFunctor] using hKbase)⟩
  let Kfib : FibredCategoryOverHom X'' X' :=
    { underlying := Kover
      preserves := by
        intro a b φ hφ
        let eia : y a ≅ H.obj a :=
          { hom := i a, inv := inv (i a)
            hom_inv_id := by simp, inv_hom_id := by simp }
        let eib : H.obj b ≅ y b :=
          { hom := inv (i b), inv := i b
            hom_inv_id := by simp, inv_hom_id := by simp }
        let _ : (structureFunctor X'.underlying).IsStronglyCartesian
            ((structureFunctor X'.underlying).map (i a)) (i a) := by
          let _ : (structureFunctor X'.underlying).IsHomLift
              ((structureFunctor X'.underlying).map (i a)) (i a) :=
            Functor.IsHomLift.map (i a)
          exact iso_is_stronglyCartesian
            (structureFunctor X'.underlying) ((structureFunctor X'.underlying).map (i a)) eia
        let _ : (structureFunctor X'.underlying).IsStronglyCartesian
            ((structureFunctor X'.underlying).map (inv (i b))) (inv (i b)) := by
          let _ : (structureFunctor X'.underlying).IsHomLift
              ((structureFunctor X'.underlying).map (inv (i b))) (inv (i b)) :=
            Functor.IsHomLift.map (inv (i b))
          exact iso_is_stronglyCartesian
            (structureFunctor X'.underlying) ((structureFunctor X'.underlying).map (inv (i b))) eib
        let _ : (structureFunctor X'.underlying).IsStronglyCartesian
            ((structureFunctor X'.underlying).map (H.map φ)) (H.map φ) :=
          h0.preserves φ hφ
        change (structureFunctor X'.underlying).IsStronglyCartesian
          ((structureFunctor X'.underlying).map (K.map φ)) (K.map φ)
        have heq : K.map φ =
            i a ≫ H.map φ ≫ inv (i b) := by
          calc
            K.map φ = (K.map φ ≫ i b) ≫ inv (i b) := by simp [Category.assoc]
            _ = (i a ≫ H.map φ) ≫ inv (i b) := by rw [hmf φ]
            _ = i a ≫ H.map φ ≫ inv (i b) := by simp [Category.assoc]
        rw [heq]
        simpa only [Functor.map_comp] using
          (inferInstance :
            (structureFunctor X'.underlying).IsStronglyCartesian
              ((structureFunctor X'.underlying).map (i a) ≫
                (structureFunctor X'.underlying).map (H.map φ) ≫
                (structureFunctor X'.underlying).map (inv (i b)))
              (i a ≫ H.map φ ≫ inv (i b))) }
  obtain ⟨ai, ⟨eaL⟩, ⟨eaR⟩⟩ := D.a_equivalence_over_C
  let k0 := FibredCategoryOverHom.comp ai D.b
  let eKfib : D.f ≅ FibredCategoryOverHom.comp k0 D.g :=
    (Bicategory.leftUnitor (B := FibredCategoryOver C) D.f).symm ≪≫
      Bicategory.whiskerRightIso (B := FibredCategoryOver C) eaR.symm D.f ≪≫
      Bicategory.associator (B := FibredCategoryOver C) ai D.a D.f ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) ai eF ≪≫
      (Bicategory.associator (B := FibredCategoryOver C) ai D.b D.g).symm
  let eK' := underlyingIsoOfFibredHomIso eKfib
  let K0 := overFunctor k0.underlying
  change p ≅ K0 ⋙ q at eK'
  let unit0 :
      FibredCategoryOverHom.comp h0 k0 ≅ FibredCategoryOverHom.id X'' :=
    Bicategory.associator (B := FibredCategoryOver C) bi D.a k0 ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) bi
        (Bicategory.associator (B := FibredCategoryOver C) D.a ai D.b).symm ≪≫
      (Bicategory.associator (B := FibredCategoryOver C) bi
        (FibredCategoryOverHom.comp D.a ai) D.b).symm ≪≫
      Bicategory.whiskerRightIso (B := FibredCategoryOver C)
        (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) bi eaL) D.b ≪≫
      Bicategory.associator (B := FibredCategoryOver C) bi
        (FibredCategoryOverHom.id X) D.b ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) bi
        (Bicategory.leftUnitor (B := FibredCategoryOver C) D.b) ≪≫ ebR
  let counit0 :
      FibredCategoryOverHom.comp k0 h0 ≅ FibredCategoryOverHom.id X' :=
    Bicategory.associator (B := FibredCategoryOver C) ai D.b h0 ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) ai
        (Bicategory.associator (B := FibredCategoryOver C) D.b bi D.a).symm ≪≫
      (Bicategory.associator (B := FibredCategoryOver C) ai
        (FibredCategoryOverHom.comp D.b bi) D.a).symm ≪≫
      Bicategory.whiskerRightIso (B := FibredCategoryOver C)
        (Bicategory.whiskerLeftIso (B := FibredCategoryOver C) ai ebL) D.a ≪≫
      Bicategory.associator (B := FibredCategoryOver C) ai
        (FibredCategoryOverHom.id X) D.a ≪≫
      Bicategory.whiskerLeftIso (B := FibredCategoryOver C) ai
        (Bicategory.leftUnitor (B := FibredCategoryOver C) D.a) ≪≫ eaR
  let unit0' := underlyingIsoOfFibredHomIso unit0
  let counit0' := underlyingIsoOfFibredHomIso counit0
  change H ⋙ K0 ≅ 𝟭 X''.underlying.left at unit0'
  change K0 ⋙ H ≅ 𝟭 X'.underlying.left at counit0'
  let hp2 := D.g_groupoid_fibred_over_Y
  let einv := eK'.symm
  let y2 (z : X'.underlying.left) :=
    Classical.choose (hp2.exists_lift (einv.inv.app z) rfl)
  let i2 (z : X'.underlying.left) : y2 z ⟶ K0.obj z :=
    Classical.choose (Classical.choose_spec (hp2.exists_lift (einv.inv.app z) rfl))
  have hi2 (z : X'.underlying.left) :
      q.IsHomLift (einv.inv.app z) (i2 z) :=
    Classical.choose_spec (Classical.choose_spec (hp2.exists_lift (einv.inv.app z) rfl))
  let hdom2 (z : X'.underlying.left) : q.obj (y2 z) = p.obj z := by
    let _ : q.IsHomLift (einv.inv.app z) (i2 z) := hi2 z
    exact CategoryTheory.IsHomLift.domain_eq q (einv.inv.app z) (i2 z)
  let basef2 {z₁ z₂ : X'.underlying.left} (f : z₁ ⟶ z₂) :
      q.obj (y2 z₁) ⟶ q.obj (y2 z₂) :=
    eqToHom (hdom2 z₁) ≫ p.map f ≫ eqToHom (hdom2 z₂).symm
  have hbase2 {z₁ z₂ : X'.underlying.left} (f : z₁ ⟶ z₂) :
      basef2 f ≫ q.map (i2 z₂) = q.map (i2 z₁ ≫ K0.map f) := by
    let _ : q.IsHomLift (einv.inv.app z₁) (i2 z₁) := hi2 z₁
    let _ : q.IsHomLift (einv.inv.app z₂) (i2 z₂) := hi2 z₂
    rw [Functor.map_comp]
    rw [CategoryTheory.IsHomLift.fac' q (einv.inv.app z₂) (i2 z₂)]
    rw [CategoryTheory.IsHomLift.fac' q (einv.inv.app z₁) (i2 z₁)]
    simp [basef2, Category.assoc]
  let m2 {z₁ z₂ : X'.underlying.left} (f : z₁ ⟶ z₂) : y2 z₁ ⟶ y2 z₂ :=
    Classical.choose ((hp2.unique_lift (i2 z₂) (i2 z₁ ≫ K0.map f) (hbase2 f)).exists)
  have hm2 {z₁ z₂ : X'.underlying.left} (f : z₁ ⟶ z₂) :
      q.IsHomLift (basef2 f) (m2 f) :=
    (Classical.choose_spec ((hp2.unique_lift (i2 z₂) (i2 z₁ ≫ K0.map f) (hbase2 f)).exists)).1
  have hmf2 {z₁ z₂ : X'.underlying.left} (f : z₁ ⟶ z₂) :
      m2 f ≫ i2 z₂ = i2 z₁ ≫ K0.map f :=
    (Classical.choose_spec ((hp2.unique_lift (i2 z₂) (i2 z₁ ≫ K0.map f) (hbase2 f)).exists)).2
  let L : X'.underlying.left ⥤ X''.underlying.left := {
    obj := y2
    map := m2
    map_id := by
      intro z
      apply (hp2.unique_lift (i2 z) (i2 z) (f := 𝟙 _) (by simp)).unique
      · refine ⟨?_, ?_⟩
        · simpa [basef2] using hm2 (𝟙 z)
        · simpa using hmf2 (𝟙 z)
      · exact ⟨inferInstance, by simp⟩
    map_comp := by
      intro z₁ z₂ z₃ f g
      apply (hp2.unique_lift (i2 z₃) (i2 z₁ ≫ K0.map (f ≫ g))
        (f := basef2 (f ≫ g)) (hbase2 (f ≫ g))).unique
      · refine ⟨?_, ?_⟩
        · exact hm2 (f ≫ g)
        · exact hmf2 (f ≫ g)
      · let _ : q.IsHomLift (basef2 f) (m2 f) := hm2 f
        let _ : q.IsHomLift (basef2 g) (m2 g) := hm2 g
        have hcomp : q.IsHomLift (basef2 f ≫ basef2 g) (m2 f ≫ m2 g) := inferInstance
        refine ⟨?_, ?_⟩
        · simpa [basef2, Category.assoc] using hcomp
        · rw [Category.assoc, hmf2 g, ← Category.assoc, hmf2 f, Category.assoc,
            ← Functor.map_comp]
  }
  have hLq : L ⋙ q = p := by
    refine CategoryTheory.Functor.ext (fun z => ?_) (fun z₁ z₂ f => ?_)
    · exact hdom2 z
    · let _ : q.IsHomLift (basef2 f) (m2 f) := hm2 f
      simpa [L, basef2, Category.assoc] using
        (CategoryTheory.IsHomLift.fac' q (basef2 f) (m2 f))
  have hi2_iso (z : X'.underlying.left) : IsIso (i2 z) := by
    let _ : q.IsHomLift (einv.inv.app z) (i2 z) := hi2 z
    let _ : q.IsStronglyCartesian (q.map (i2 z)) (i2 z) :=
      fibredInGroupoids_all_morphisms_stronglyCartesian q hp2 (i2 z)
    let _ : IsIso (q.map (i2 z)) := by
      rw [CategoryTheory.IsHomLift.fac' q (einv.inv.app z) (i2 z)]
      infer_instance
    exact stronglyCartesian_of_base_isIso q (q.map (i2 z)) (i2 z)
  let η2 : L ≅ K0 := NatIso.ofComponents (fun z => by
    let _ : IsIso (i2 z) := hi2_iso z
    exact asIso (i2 z)) (by
      intro z₁ z₂ f
      exact hmf2 f)
  have hηover (z : X''.underlying.left) :
      (structureFunctor X'.underlying).map (η.hom.app z) =
        overIdentityComponent Kover h0.underlying z := by
    dsimp [overIdentityComponent, Kover, overFunctor]
    change (structureFunctor X'.underlying).map (i z) = _
    have hfac := CategoryTheory.IsHomLift.fac' p (eH'.inv.app z) (i z)
    have hfi := Functor.congr_hom (overFunctor_comm D.f.underlying) (i z)
    have hE := eH.inv.over z
    change (structureFunctor Y.underlying).map (eH'.inv.app z) =
      overIdentityComponent
        D.g.underlying (FibredCategoryOverHom.comp h0 D.f).underlying z at hE
    have hHbase : H ⋙ structureFunctor X'.underlying = structureFunctor X''.underlying := by
      simpa only [H] using (overFunctor_comm h0.underlying)
    have hbase_eq :
        (structureFunctor X'.underlying).obj (K.obj z) =
          (structureFunctor X'.underlying).obj (H.obj z) := by
      exact
        (congrArg (fun K : X''.underlying.left ⥤ C => K.obj z) hKbase).trans
          (congrArg (fun K : X''.underlying.left ⥤ C => K.obj z) hHbase).symm
    change (structureFunctor X'.underlying).map (i z) = eqToHom hbase_eq
    have hfi_heq :
        (structureFunctor X'.underlying).map (i z) ≍
          (structureFunctor Y.underlying).map (p.map (i z)) := by
      have hh :=
        (conj_eqToHom_iff_heq
          ((overFunctor D.f.underlying ⋙ structureFunctor Y.underlying).map (i z))
          ((structureFunctor X'.underlying).map (i z))
          (Functor.congr_obj (overFunctor_comm D.f.underlying) (y z))
          (Functor.congr_obj (overFunctor_comm D.f.underlying) (H.obj z))).1 hfi
      simpa only [p, Functor.comp_map] using hh.symm
    have hfac_heq :
        (structureFunctor Y.underlying).map (p.map (i z)) ≍
          (structureFunctor Y.underlying).map (eH'.inv.app z) := by
      rw [hfac]
      simp [Functor.map_comp, eqToHom_map]
    have hE_heq :
        (structureFunctor Y.underlying).map (eH'.inv.app z) ≍
          𝟙 ((structureFunctor Y.underlying).obj (q.obj z)) := by
      rw [hE]
      exact eqToHom_heq_id_dom _ _ _
    have hKq :
        (structureFunctor X'.underlying).obj (K.obj z) =
          (structureFunctor Y.underlying).obj (q.obj z) := by
      exact
        (congrArg (fun K : X''.underlying.left ⥤ C => K.obj z) hKbase).trans
          (congrArg (fun K : X''.underlying.left ⥤ C => K.obj z)
            (overFunctor_comm D.g.underlying)).symm
    have hbase_heq :
        (structureFunctor X'.underlying).map (i z) ≍
          𝟙 ((structureFunctor X'.underlying).obj (K.obj z)) := by
      exact
        hfi_heq.trans (hfac_heq.trans
          (hE_heq.trans
            ((eqToHom_heq_id_cod _ _ hKq).symm.trans
              (eqToHom_heq_id_dom _ _ hKq))))
    simpa using
      (conj_eqToHom_iff_heq
        ((structureFunctor X'.underlying).map (i z))
        (𝟙 ((structureFunctor X'.underlying).obj (K.obj z))) rfl hbase_eq.symm).2
         hbase_heq
  let _ : H.IsEquivalence :=
    Functor.IsEquivalence.mk' K0 unit0'.symm counit0'
  have hKeq : K.IsEquivalence :=
    Functor.isEquivalence_of_iso η.symm
  let _ : K.IsEquivalence := hKeq
  let eK := K.asEquivalence
  let Lobj (b : X'.underlying.left) := eK.inverse.obj b
  let eps (b : X'.underlying.left) : K.obj (Lobj b) ≅ b :=
    eK.counitIso.app b
  have hKobj (a : X''.underlying.left) :
      q.obj a = p.obj (K.obj a) :=
    (congrArg (fun R : X''.underlying.left ⥤ Y.underlying.left => R.obj a) hKp).symm
  have hKobj' (a : X''.underlying.left) :
      p.obj (K.obj a) = q.obj a := (hKobj a).symm
  let z (b : X'.underlying.left) :=
    Classical.choose
      (hp2.exists_lift (p.map (eps b).inv) (hKobj (Lobj b)))
  let j (b : X'.underlying.left) : z b ⟶ Lobj b :=
    Classical.choose
      (Classical.choose_spec
        (hp2.exists_lift (p.map (eps b).inv) (hKobj (Lobj b))))
  have hj (b : X'.underlying.left) :
      q.IsHomLift (p.map (eps b).inv) (j b) :=
    Classical.choose_spec
      (Classical.choose_spec
        (hp2.exists_lift (p.map (eps b).inv) (hKobj (Lobj b))))
  let hz (b : X'.underlying.left) : q.obj (z b) = p.obj b := by
    let _ : q.IsHomLift (p.map (eps b).inv) (j b) := hj b
    exact CategoryTheory.IsHomLift.domain_eq q (p.map (eps b).inv) (j b)
  let vhom (b : X'.underlying.left) : K.obj (z b) ⟶ b :=
    K.map (j b) ≫ (eps b).hom
  have hvmap (b : X'.underlying.left) :
      p.map (vhom b) =
        eqToHom ((hKobj (z b)).symm.trans (hz b)) := by
    let _ : q.IsHomLift (p.map (eps b).inv) (j b) := hj b
    have hjfac := CategoryTheory.IsHomLift.fac' q (p.map (eps b).inv) (j b)
    have hKj := Functor.congr_hom hKp (j b)
    have hKj' :
        p.map (K.map (j b)) =
          eqToHom (hKobj' (z b)) ≫ q.map (j b) ≫
            eqToHom (hKobj' (Lobj b)).symm := by
      simpa only [Functor.comp_map] using hKj
    rw [Functor.map_comp, hKj']
    simp [hjfac, Category.assoc]
  have hj_iso (b : X'.underlying.left) : IsIso (j b) := by
    let _ : q.IsHomLift (p.map (eps b).inv) (j b) := hj b
    let _ : q.IsStronglyCartesian (q.map (j b)) (j b) :=
      fibredInGroupoids_all_morphisms_stronglyCartesian q hp2 (j b)
    let _ : IsIso (q.map (j b)) := by
      rw [CategoryTheory.IsHomLift.fac' q (p.map (eps b).inv) (j b)]
      infer_instance
    exact stronglyCartesian_of_base_isIso q (q.map (j b)) (j b)
  let v (b : X'.underlying.left) : K.obj (z b) ≅ b := by
    let _ : IsIso (j b) := hj_iso b
    let _ : IsIso (K.map (j b)) := Functor.map_isIso K (j b)
    let _ : IsIso (vhom b) := inferInstance
    exact asIso (vhom b)
  have hv (b : X'.underlying.left) :
      p.map (v b).hom =
        eqToHom ((hKobj (z b)).symm.trans (hz b)) := by
    simpa [v] using hvmap b
  have hv_inv (b : X'.underlying.left) :
      p.map (v b).inv =
        eqToHom ((hKobj (z b)).symm.trans (hz b)).symm := by
    apply (cancel_mono (p.map (v b).hom)).1
    rw [← p.map_comp, hv]
    simp
  let raw {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      K.obj (z b₁) ⟶ K.obj (z b₂) :=
    (v b₁).hom ≫ f ≫ (v b₂).inv
  let lm {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      z b₁ ⟶ z b₂ := K.preimage (raw f)
  have hlm {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      K.map (lm f) = raw f := K.map_preimage _
  let Ls : X'.underlying.left ⥤ X''.underlying.left := {
    obj := z
    map := lm
    map_id := by
      intro b
      apply hKeq.faithful.map_injective
      rw [hlm]
      simp [raw]
    map_comp := by
      intro b₁ b₂ b₃ f g
      apply hKeq.faithful.map_injective
      rw [Functor.map_comp, hlm, hlm, hlm]
      simp [raw, Category.assoc]
  }
  have hLsmap {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      Ls.map f = lm f := rfl
  have hKlm {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      p.map (K.map (lm f)) =
        eqToHom (hKobj' (z b₁)) ≫ q.map (lm f) ≫
          eqToHom (hKobj' (z b₂)).symm := by
    simpa only [Functor.comp_map] using Functor.congr_hom hKp (lm f)
  have hLsmap_base {b₁ b₂ : X'.underlying.left} (f : b₁ ⟶ b₂) :
      q.map (Ls.map f) =
        eqToHom (hz b₁) ≫ p.map f ≫ eqToHom (hz b₂).symm := by
    calc
      q.map (Ls.map f) =
          eqToHom ((hKobj' (z b₁)).symm) ≫
            p.map (K.map (lm f)) ≫ eqToHom (hKobj' (z b₂)) := by
        rw [hLsmap, hKlm]
        simp
      _ = eqToHom (hz b₁) ≫ p.map f ≫ eqToHom (hz b₂).symm := by
        simp only [hlm, raw, Functor.map_comp, Category.assoc]
        rw [hv, hv_inv]
        simp [eqToHom_trans]
  have hLsq : Ls ⋙ q = p := by
    refine CategoryTheory.Functor.ext (fun b => hz b) (fun b₁ b₂ f => ?_)
    exact hLsmap_base f
  let counit : Ls ⋙ K ≅ 𝟭 X'.underlying.left :=
    NatIso.ofComponents v (by
      intro b₁ b₂ f
      change K.map (Ls.map f) ≫ (v b₂).hom = (v b₁).hom ≫ f
      rw [hLsmap, hlm]
      simp [raw, Category.assoc])
  let uHom (a : X''.underlying.left) :
      a ⟶ z (K.obj a) :=
    K.preimage ((v (K.obj a)).inv)
  let uInv (a : X''.underlying.left) :
      z (K.obj a) ⟶ a :=
    K.preimage ((v (K.obj a)).hom)
  have huHom (a : X''.underlying.left) :
      K.map (uHom a) = (v (K.obj a)).inv := K.map_preimage _
  have huInv (a : X''.underlying.left) :
      K.map (uInv a) = (v (K.obj a)).hom := K.map_preimage _
  let uIso (a : X''.underlying.left) : a ≅ z (K.obj a) := {
    hom := uHom a
    inv := uInv a
    hom_inv_id := by
      apply hKeq.faithful.map_injective
      rw [Functor.map_comp, huHom, huInv]
      simp
    inv_hom_id := by
      apply hKeq.faithful.map_injective
      rw [Functor.map_comp, huInv, huHom]
      simp
  }
  let unitForward : 𝟭 X''.underlying.left ≅ K ⋙ Ls :=
    NatIso.ofComponents uIso (by
      intro a₁ a₂ f
      apply hKeq.faithful.map_injective
      change K.map (f ≫ uHom a₂) =
        K.map (uHom a₁ ≫ Ls.map (K.map f))
      simp only [Functor.map_comp, huHom, hLsmap, hlm]
      simp [raw])
  let unit := unitForward.symm
  have hqu (a : X''.underlying.left) :
      q.map (uHom a) =
        eqToHom ((hKobj a).trans (hz (K.obj a)).symm) := by
    have hKuh := Functor.congr_hom hKp (uHom a)
    have hKuh' :
        p.map (K.map (uHom a)) =
          eqToHom (hKobj' a) ≫ q.map (uHom a) ≫
            eqToHom (hKobj' (z (K.obj a))).symm := by
      simpa only [Functor.comp_map] using hKuh
    rw [huHom, hv_inv] at hKuh'
    apply (cancel_epi (eqToHom (hKobj' a))).1
    apply (cancel_mono (eqToHom ((hKobj' (z (K.obj a))).symm))).1
    simpa only [Category.assoc, eqToHom_trans] using hKuh'.symm
  have hqu_inv (a : X''.underlying.left) :
      q.map (uInv a) =
        eqToHom ((hKobj a).trans (hz (K.obj a)).symm).symm := by
    let _ : IsIso (uHom a) :=
      ⟨⟨uInv a, (uIso a).hom_inv_id, (uIso a).inv_hom_id⟩⟩
    let _ : IsIso (q.map (uHom a)) := Functor.map_isIso q (uHom a)
    apply (cancel_mono (q.map (uHom a))).1
    rw [← q.map_comp, hqu, (uIso a).inv_hom_id, q.map_id]
    simp [eqToHom_trans]
  let overUnit : (K ⋙ Ls) ⋙ q = (𝟭 X''.underlying.left) ⋙ q := by
    simp only [Functor.assoc]
    rw [hLsq, hKp]
    simp only [Functor.id_comp]
  let overCounit : (Ls ⋙ K) ⋙ p = (𝟭 X'.underlying.left) ⋙ p := by
    simp only [Functor.assoc]
    rw [hKp, hLsq]
    simp only [Functor.id_comp]
  have hunitOver : IsNatIsoOver q unit overUnit := by
    intro a
    change q.map (uInv a) = _
    rw [hqu_inv]
  have hcounitOver : IsNatIsoOver p counit overCounit := by
    intro b
    change p.map ((v b).hom) = _
    rw [hv]
  let eKH : Kover ≅ h0.underlying :=
    overNatIsoOfUnderlying η hηover
  let eFib : Kfib ≅ h0 :=
    fibredHomIsoOfUnderlying eKH
  let eFibLeft : D.b.comp Kfib ≅ D.b.comp h0 :=
    Bicategory.whiskerLeftIso (B := FibredCategoryOver C) D.b eFib
  let comparison : D.b.comp Kfib ≅ D.a :=
    eFibLeft ≪≫ eba
  refine ⟨Kfib, ?_, ⟨comparison⟩⟩
  change IsEquivalenceOverFunctor q p K
  exact ⟨Ls, hKp, hLsq, ⟨unit, overUnit, hunitOver⟩,
    ⟨counit, overCounit, hcounitOver⟩⟩

/- Proof roadmap: apply `amelioration_unique`, retain its comparison functor
and fibred-hom isomorphism, then map that isomorphism to underlying functors.
Rewrite both sides with `left_strict` and `right_strict`; the triangle
2-isomorphisms then show every component maps to the required `eqToHom`, which
is exactly `IsNatIsoOver`.  This is waiting on the same strict over-base
whiskering lemmas as `amelioration_unique`. -/
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

/-! ## Presheaves of categories -/

/- A presheaf of categories is represented by the canonical pseudofunctor
   from `Cᵒᵖ` to `Cat`.  The CoGrothendieck construction below is Mathlib's
   source-faithful implementation of the displayed objects, morphisms, and
   composition law. -/

abbrev CategoryPresheaf (C : Type u') [Category.{v'} C] :=
  PseudofunctorFromCategory Cᵒᵖ (Cat.{v', u'})

abbrev categoryPresheafCategory
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) :=
  Pseudofunctor.CoGrothendieck F

abbrev categoryPresheafProjection
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) :
    categoryPresheafCategory F ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget F

abbrev categoryPresheafObject
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) :=
  categoryPresheafCategory F

abbrev categoryPresheafHom
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C)
    {X Y : categoryPresheafCategory F} :=
  Pseudofunctor.CoGrothendieck.Hom X Y

abbrev categoryPresheafRestriction
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {V U : C} (f : V ⟶ U) :
    F.obj ⟨Opposite.op U⟩ ⥤ F.obj ⟨Opposite.op V⟩ :=
  (F.map f.op.toLoc).toFunctor

theorem categoryPresheafRestriction_comp
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    Nonempty (categoryPresheafRestriction F (g ≫ f) ≅
      categoryPresheafRestriction F f ⋙ categoryPresheafRestriction F g) := by
  refine ⟨?_⟩
  change (F.map (g ≫ f).op.toLoc).toFunctor ≅
    (F.map f.op.toLoc).toFunctor ⋙ (F.map g.op.toLoc).toFunctor
  convert CategoryTheory.Cat.Hom.toNatIso (F.mapComp f.op.toLoc g.op.toLoc) using 1 <;> rfl

@[simp]
theorem categoryPresheafProjection_obj
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) (X : categoryPresheafCategory F) :
    (categoryPresheafProjection F).obj X = X.base :=
  rfl

@[simp]
theorem categoryPresheafProjection_map
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C)
    {X Y : categoryPresheafCategory F} (f : X ⟶ Y) :
    (categoryPresheafProjection F).map f = f.base :=
  rfl

@[simp]
theorem categoryPresheaf_id_base
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) (X : categoryPresheafCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem categoryPresheaf_comp_base
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C)
    {X Y Z : categoryPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

theorem categoryPresheaf_comp_fiber
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C)
    {X Y Z : categoryPresheafCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        (F.map f.base.op.toLoc).toFunctor.map g.fiber ≫
        (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

abbrev categoryPresheafCartesianDomain
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {V U : C} (f : V ⟶ U)
    (x : F.obj ⟨op U⟩) : categoryPresheafCategory F :=
  Pseudofunctor.CoGrothendieck.domainCartesianLift x f

abbrev categoryPresheafCartesianLift
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {V U : C} (f : V ⟶ U)
    (x : F.obj ⟨op U⟩) :
    categoryPresheafCartesianDomain F f x ⟶
      (⟨U, x⟩ : categoryPresheafCategory F) :=
  Pseudofunctor.CoGrothendieck.cartesianLift x f

theorem categoryPresheafCartesianLift_isHomLift
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {V U : C} (f : V ⟶ U)
    (x : F.obj ⟨op U⟩) :
    (categoryPresheafProjection F).IsHomLift f
      (categoryPresheafCartesianLift F f x) := by
  infer_instance

theorem categoryPresheafCartesianLift_isStronglyCartesian
    {C : Type u'} [Category.{v'} C]
    (F : CategoryPresheaf C) {V U : C} (f : V ⟶ U)
    (x : F.obj ⟨op U⟩) :
    Functor.IsStronglyCartesian (categoryPresheafProjection F) f
      (categoryPresheafCartesianLift F f x) := by
  exact Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := F) x f

theorem categoryPresheafProjection_isFibered
    {C : Type u'} [Category.{v'} C] (F : CategoryPresheaf C) :
    (categoryPresheafProjection F).IsFibered := by
  infer_instance

def IsomorphicOverBase
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) : Prop :=
  ∃ (F : S ⥤ T) (G : T ⥤ S),
    F ⋙ q = p ∧ G ⋙ p = q ∧ F ⋙ G = 𝟭 S ∧ G ⋙ F = 𝟭 T

def IsSplitFibredCategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : Prop :=
  p.IsFibered ∧
    ∃ F : CategoryPresheaf C,
      IsomorphicOverBase p (categoryPresheafProjection F)

theorem categoryPresheafProjection_isSplit
    {C : Type u'} [Category.{v'} C] (F : CategoryPresheaf C) :
    IsSplitFibredCategory (categoryPresheafProjection F) := by
  constructor
  · exact categoryPresheafProjection_isFibered F
  · exact ⟨F, 𝟭 _, 𝟭 _, Functor.id_comp _, Functor.id_comp _,
      Functor.id_comp _, Functor.id_comp _⟩

def isStrictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered]
    (P : PullbackChoice p) : Prop :=
  ∀ {W V U : C} (g : W ⟶ V) (f : V ⟶ U),
    P.pullbackFunctor (g ≫ f) =
      P.pullbackFunctor f ⋙ P.pullbackFunctor g

theorem isSplitFibredCategory_iff_exists_strictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    IsSplitFibredCategory p ↔
      ∃ P : PullbackChoice p, P.IsUnital ∧ isStrictPullbackChoice P := by
  sorry

/- The explicit strictification category in the proof of the source's last
   lemma.  Its objects are `(x, f : V ⟶ U)` with `x` in the fibre over `U`,
   and its morphisms are the underlying arrows between the chosen pullbacks. -/

structure CategoryPresheafStrictificationObject
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  V : C
  U : C
  f : V ⟶ U
  x : Functor.Fiber p U

def categoryPresheafStrictificationObjectOf
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    CategoryPresheafStrictificationObject p P where
  V := p.obj x
  U := p.obj x
  f := 𝟙 (p.obj x)
  x := ⟨x, rfl⟩

def categoryPresheafStrictificationReindexObject
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W : C} (A : CategoryPresheafStrictificationObject p P)
    (g : W ⟶ A.V) : CategoryPresheafStrictificationObject p P where
  V := W
  U := A.U
  f := g ≫ A.f
  x := A.x

theorem categoryPresheafStrictificationReindexObject_comp
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W V : C} (h : W ⟶ V)
    (A : CategoryPresheafStrictificationObject p P) (g : V ⟶ A.V) :
    categoryPresheafStrictificationReindexObject
        (categoryPresheafStrictificationReindexObject A g) h =
      categoryPresheafStrictificationReindexObject A (h ≫ g) := by
  cases A
  simp [categoryPresheafStrictificationReindexObject, Category.assoc]

def categoryPresheafStrictificationPullback
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : CategoryPresheafStrictificationObject p P) :
    Functor.Fiber p A.V :=
  P.pullback A.f A.x

structure CategoryPresheafStrictificationHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {A B : CategoryPresheafStrictificationObject p P} where
  hom : (categoryPresheafStrictificationPullback A).1 ⟶
    (categoryPresheafStrictificationPullback B).1

def categoryPresheafStrictificationHomBase
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : CategoryPresheafStrictificationObject p P}
    (f : CategoryPresheafStrictificationHom (A := A) (B := B) P) :
      A.V ⟶ B.V :=
  eqToHom (categoryPresheafStrictificationPullback A).2.symm ≫
    p.map f.hom ≫ eqToHom (categoryPresheafStrictificationPullback B).2

@[ext]
theorem categoryPresheafStrictificationHom_ext
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : CategoryPresheafStrictificationObject p P}
    {f g : CategoryPresheafStrictificationHom (A := A) (B := B) P}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

abbrev CategoryPresheafStrictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :=
  CategoryPresheafStrictificationObject p P

instance categoryPresheafStrictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    Category (CategoryPresheafStrictificationCategory p P) where
  Hom A B := CategoryPresheafStrictificationHom (A := A) (B := B) P
  id A := { hom := 𝟙 (categoryPresheafStrictificationPullback A).1 }
  comp f g := { hom := f.hom ≫ g.hom }
  id_comp f := by
    apply categoryPresheafStrictificationHom_ext
    simp
  comp_id f := by
    apply categoryPresheafStrictificationHom_ext
    simp
  assoc f g h := by
    apply categoryPresheafStrictificationHom_ext
    simp [Category.assoc]

def categoryPresheafStrictificationProjection
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    CategoryPresheafStrictificationCategory p P ⥤ C where
  obj A := A.V
  map f := categoryPresheafStrictificationHomBase f
  map_id := by
    intro A
    change eqToHom _ ≫ p.map (𝟙 _) ≫ eqToHom _ = _
    simp
  map_comp := by
    intro A B D f g
    change eqToHom _ ≫ p.map (f.hom ≫ g.hom) ≫ eqToHom _ =
      (eqToHom _ ≫ p.map f.hom ≫ eqToHom _) ≫
        (eqToHom _ ≫ p.map g.hom ≫ eqToHom _)
    simp [Functor.map_comp, Category.assoc]

theorem categoryPresheafStrictificationProjection_isFibered
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    (categoryPresheafStrictificationProjection P).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro B R f
  let A := categoryPresheafStrictificationReindexObject B f
  let hBStrong : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) :=
    P.pullbackMap_isStronglyCartesian B.f B.x
  let : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) := hBStrong
  let : p.IsStronglyCartesian (f ≫ B.f)
      (P.pullbackMap (f ≫ B.f) B.x) :=
    P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
  let : p.IsHomLift (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x) := by
    exact @Functor.IsStronglyCartesian.toIsHomLift _ _ _ _ p _ _ _ _
      (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x)
  let φ : (categoryPresheafStrictificationPullback A).1 ⟶
      (categoryPresheafStrictificationPullback B).1 :=
    @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      B.f (P.pullbackMap B.f B.x)
      (P.pullbackMap_isStronglyCartesian B.f B.x)
      _ _ f (f ≫ B.f) rfl
      (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x).toIsHomLift
  have hφlift : p.IsHomLift f φ := by
    dsimp [φ]
    exact Functor.IsStronglyCartesian.map_isHomLift p B.f
      (P.pullbackMap B.f B.x) (f' := f ≫ B.f) (g := f) rfl
      (P.pullbackMap (f ≫ B.f) B.x)
  let : p.IsHomLift f φ := hφlift
  have hφstrong : p.IsStronglyCartesian f φ := by
    have hfac : φ ≫ P.pullbackMap B.f B.x =
        P.pullbackMap (f ≫ B.f) B.x := by
      dsimp [φ]
      exact Functor.IsStronglyCartesian.fac p B.f
        (P.pullbackMap B.f B.x) (f' := f ≫ B.f) (g := f) rfl
        (P.pullbackMap (f ≫ B.f) B.x)
    have hcompStrong : p.IsStronglyCartesian (f ≫ B.f)
        (φ ≫ P.pullbackMap B.f B.x) := by
      rw [hfac]
      exact P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
    let : p.IsStronglyCartesian (f ≫ B.f)
        (φ ≫ P.pullbackMap B.f B.x) := hcompStrong
    exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _ f B.f φ
      (P.pullbackMap B.f B.x) hBStrong hcompStrong hφlift
  let κ : A ⟶ B := { hom := φ }
  have hκbase : (categoryPresheafStrictificationProjection P).map κ = f := by
    change eqToHom _ ≫ p.map φ ≫ eqToHom _ = f
    exact (CategoryTheory.IsHomLift.fac p f φ).symm
  have hκlift : (categoryPresheafStrictificationProjection P).IsHomLift f κ := by
    have h := (inferInstance :
      (categoryPresheafStrictificationProjection P).IsHomLift
        ((categoryPresheafStrictificationProjection P).map κ) κ)
    rw [hκbase] at h
    exact h
  let : (categoryPresheafStrictificationProjection P).IsHomLift f κ := hκlift
  have hκstrong : (categoryPresheafStrictificationProjection P).IsStronglyCartesian f κ := by
    let : p.IsStronglyCartesian f φ := hφstrong
    constructor
    intro X g τ hτ
    let eX := (categoryPresheafStrictificationPullback X).2
    let eA := (categoryPresheafStrictificationPullback A).2
    let eB := (categoryPresheafStrictificationPullback B).2
    have hτmap : g ≫ f = (categoryPresheafStrictificationProjection P).map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift
        (categoryPresheafStrictificationProjection P) (g ≫ f) τ
    have hτmap' : g ≫ f =
        eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB := by
      simpa [categoryPresheafStrictificationProjection,
        categoryPresheafStrictificationHomBase] using hτmap
    let g₀ : p.obj ((categoryPresheafStrictificationPullback X).1) ⟶ R :=
      eqToHom eX ≫ g
    have hτp : p.IsHomLift (g₀ ≫ f) τ.hom := by
      apply CategoryTheory.IsHomLift.of_fac p (g₀ ≫ f) τ.hom rfl eB
      dsimp [g₀]
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((categoryPresheafStrictificationPullback X).1)) := by
        simp
      have hAssoc : (eqToHom eX ≫ g) ≫ f =
          eqToHom eX ≫ (g ≫ f) := Category.assoc _ _ _
      have hRewrite : eqToHom eX ≫ (g ≫ f) =
          eqToHom eX ≫
            (eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB) := by
        exact congrArg (fun k => eqToHom eX ≫ k) hτmap'
      rw [hAssoc, hRewrite]
      have hcancel' := congrArg
        (fun k => k ≫ p.map τ.hom ≫ eqToHom eB) hcancel
      convert hcancel' using 1
      simp only [Category.assoc]
      rfl
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p f φ
        g₀ (g₀ ≫ f) rfl τ.hom
    let : p.IsHomLift g₀ χ := hχ
    let χ' : X ⟶ A := { hom := χ }
    have hχfac' : g₀ = p.map χ ≫ eqToHom eA := by
      let d := CategoryTheory.IsHomLift.domain_eq p g₀ χ
      let c := CategoryTheory.IsHomLift.codomain_eq p g₀ χ
      have hfac : g₀ = eqToHom d.symm ≫ p.map χ ≫ eqToHom c := by
        exact CategoryTheory.IsHomLift.fac p g₀ χ
      rw [hfac]
      have hEq : c = eA := by
        apply Subsingleton.elim
      have hDom : eqToHom d.symm =
          𝟙 (p.obj ((categoryPresheafStrictificationPullback X).1)) := by
        have hd : d =
            (rfl : p.obj ((categoryPresheafStrictificationPullback X).1) =
              p.obj ((categoryPresheafStrictificationPullback X).1)) := by
          apply Subsingleton.elim
        exact congrArg
          (fun h : p.obj ((categoryPresheafStrictificationPullback X).1) =
              p.obj ((categoryPresheafStrictificationPullback X).1) => eqToHom h.symm) hd
      rw [hDom, hEq, Category.id_comp]
      rfl
    have hχbase : (categoryPresheafStrictificationProjection P).map χ' = g := by
      change eqToHom eX.symm ≫ p.map χ ≫ eqToHom eA = g
      change X.V ⟶ R at g
      rw [← hχfac']
      dsimp [g₀]
      have hcancel : eqToHom eX.symm ≫ eqToHom eX =
          𝟙 X.V := by simp
      calc
        eqToHom eX.symm ≫ eqToHom eX ≫ g =
            (eqToHom eX.symm ≫ eqToHom eX) ≫ g :=
          (Category.assoc _ _ _).symm
        _ = (𝟙 X.V) ≫ g := congrArg (fun k => k ≫ g) hcancel
        _ = g := by simp
    have hχ'lift : (categoryPresheafStrictificationProjection P).IsHomLift g χ' := by
      have h := (inferInstance :
        (categoryPresheafStrictificationProjection P).IsHomLift
          ((categoryPresheafStrictificationProjection P).map χ') χ')
      rw [hχbase] at h
      exact h
    let : (categoryPresheafStrictificationProjection P).IsHomLift g χ' := hχ'lift
    have hχcomp : χ' ≫ κ = τ := by
      apply categoryPresheafStrictificationHom_ext
      exact hχfac
    refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
    intro χ'' hχ''
    have : (categoryPresheafStrictificationProjection P).IsHomLift g χ'' := hχ''.1
    have hχ''map : g = (categoryPresheafStrictificationProjection P).map χ'' := by
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift C
        (CategoryPresheafStrictificationCategory p P) _ _
        (categoryPresheafStrictificationProjection P) X A g χ'' hχ''.1
    have hχ''p : p.IsHomLift g₀ χ''.hom := by
      apply CategoryTheory.IsHomLift.of_fac p g₀ χ''.hom rfl eA
      have hχ''map' : g =
          eqToHom eX.symm ≫ p.map χ''.hom ≫ eqToHom eA := by
        simpa [categoryPresheafStrictificationProjection,
          categoryPresheafStrictificationHomBase] using hχ''map
      dsimp [g₀]
      rw [hχ''map']
      change p.obj ((categoryPresheafStrictificationPullback A).1) = R at eA
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((categoryPresheafStrictificationPullback X).1)) := by
        simp
      have hcancel' := congrArg
        (fun k => k ≫ p.map χ''.hom ≫ eqToHom eA) hcancel
      convert hcancel' using 1
      simp only [Category.assoc]
      rfl
    have hχ''comp : χ''.hom ≫ φ = τ.hom := by
      have hcomp := congrArg (fun h : X ⟶ B => h.hom) hχ''.2
      dsimp [κ] at hcomp
      exact hcomp
    have hhom : χ''.hom = χ :=
      hχuniq χ''.hom ⟨hχ''p, hχ''comp⟩
    exact categoryPresheafStrictificationHom_ext hhom
  exact ⟨A, κ, hκstrong⟩

private def categoryPresheafStrictificationInverse
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    CategoryPresheafStrictificationCategory p P ⥤ S where
  obj A := (categoryPresheafStrictificationPullback A).1
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

private def categoryPresheafStrictificationFunctorHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {x y : S} (φ : x ⟶ y) :
    CategoryPresheafStrictificationHom P
      (A := categoryPresheafStrictificationObjectOf P x)
      (B := categoryPresheafStrictificationObjectOf P y) where
  hom := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
    (𝟙 (p.obj y))
    (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩)
    (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj y)) ⟨y, rfl⟩)
    _ _ (p.map φ) (p.map φ) (by simp)
    (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ)
    (by
      let : p.IsStronglyCartesian (𝟙 (p.obj x))
          (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
        P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩
      change p.IsHomLift (p.map φ)
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ)
      simpa using (IsHomLift.comp p (𝟙 (p.obj x)) (p.map φ)
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) φ))

private theorem categoryPresheafStrictificationFunctorHom_isHomLift
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {x y : S} (φ : x ⟶ y) :
    p.IsHomLift (p.map φ)
      (categoryPresheafStrictificationFunctorHom P φ).hom := by
  unfold categoryPresheafStrictificationFunctorHom
  let : p.IsStronglyCartesian (𝟙 (p.obj y))
      (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩) :=
    P.pullbackMap_isStronglyCartesian _ _
  let : p.IsStronglyCartesian (𝟙 (p.obj x))
      (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
    P.pullbackMap_isStronglyCartesian _ _
  let : p.IsHomLift (p.map φ)
      (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ) := by
    simpa using (IsHomLift.comp p (𝟙 (p.obj x)) (p.map φ)
      (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) φ)
  change p.IsHomLift (p.map φ)
    (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      (𝟙 (p.obj y)) (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩) _
      _ _ (p.map φ) (p.map φ) (by simp)
      (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ) _)
  exact Functor.IsStronglyCartesian.map_isHomLift p
    (𝟙 (p.obj y)) (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩)
    (f' := p.map φ) (g := p.map φ) (by simp)
    (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ)

private def categoryPresheafStrictificationFunctor
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    S ⥤ CategoryPresheafStrictificationCategory p P where
  obj x := categoryPresheafStrictificationObjectOf P x
  map φ := categoryPresheafStrictificationFunctorHom P φ
  map_id x := by
    apply categoryPresheafStrictificationHom_ext
    change (categoryPresheafStrictificationFunctorHom P (𝟙 x)).hom = 𝟙 _
    let : p.IsStronglyCartesian (𝟙 (p.obj x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
      P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩
    let hsource' : p.IsHomLift (p.map (𝟙 x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ 𝟙 x) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj x)) (p.map (𝟙 x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) (𝟙 x))
    let hψ : p.IsHomLift (p.map (𝟙 x))
        (categoryPresheafStrictificationFunctorHom P (𝟙 x)).hom := by
      exact categoryPresheafStrictificationFunctorHom_isHomLift P (𝟙 x)
    let hψ' : p.IsHomLift (p.map (𝟙 x))
        (𝟙 (Functor.Fiber.fiberInclusion.obj
          (P.pullback (𝟙 (p.obj x)) ⟨x, rfl⟩))) := by
      rw [p.map_id]
      exact IsHomLift.id (P.pullback (𝟙 (p.obj x)) ⟨x, rfl⟩).2
    have hEq := @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 (p.obj x)) (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩)
      (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩)
      (p.obj x) (Functor.Fiber.fiberInclusion.obj
        (P.pullback (𝟙 (p.obj x)) ⟨x, rfl⟩))
      (p.map (𝟙 x)) (categoryPresheafStrictificationFunctorHom P (𝟙 x)).hom
      (𝟙 _) hψ hψ' (by
        have hfac : (categoryPresheafStrictificationFunctorHom P (𝟙 x)).hom ≫
              P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ =
            P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ 𝟙 x := by
          change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
            (𝟙 (p.obj x)) (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩)
            (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩)
            _ _ (p.map (𝟙 x)) (p.map (𝟙 x)) (by simp)
            (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ 𝟙 x) hsource') ≫
              P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ = _
          simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
            (𝟙 (p.obj x)) (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩)
            (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩)
            (p.obj x) (Functor.Fiber.fiberInclusion.obj
              (P.pullback (𝟙 (p.obj x)) ⟨x, rfl⟩))
            (p.map (𝟙 x)) (p.map (𝟙 x)) (by simp)
            (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ 𝟙 x) hsource')
        exact hfac.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    exact hEq
  map_comp {X Y Z} f g := by
    apply categoryPresheafStrictificationHom_ext
    change (categoryPresheafStrictificationFunctorHom P (f ≫ g)).hom =
      (categoryPresheafStrictificationFunctorHom P f).hom ≫
        (categoryPresheafStrictificationFunctorHom P g).hom
    let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
    let xY : Functor.Fiber p (p.obj Y) := ⟨Y, rfl⟩
    let xZ : Functor.Fiber p (p.obj Z) := ⟨Z, rfl⟩
    let uX := P.pullbackMap (𝟙 (p.obj X)) xX
    let uY := P.pullbackMap (𝟙 (p.obj Y)) xY
    let uZ := P.pullbackMap (𝟙 (p.obj Z)) xZ
    let : p.IsStronglyCartesian (𝟙 (p.obj Z)) uZ :=
      P.pullbackMap_isStronglyCartesian _ _
    let : p.IsStronglyCartesian (𝟙 (p.obj Y)) uY :=
      P.pullbackMap_isStronglyCartesian _ _
    let : p.IsStronglyCartesian (𝟙 (p.obj X)) uX :=
      P.pullbackMap_isStronglyCartesian _ _
    have hsource_fg : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map (f ≫ g))
        uX (f ≫ g))
    let : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := hsource_fg
    let : p.IsHomLift (p.map f)
        (categoryPresheafStrictificationFunctorHom P f).hom :=
      categoryPresheafStrictificationFunctorHom_isHomLift P f
    let : p.IsHomLift (p.map g)
        (categoryPresheafStrictificationFunctorHom P g).hom :=
      categoryPresheafStrictificationFunctorHom_isHomLift P g
    let : p.IsHomLift (p.map f ≫ p.map g)
        (uX ≫ (f ≫ g)) := by
      simpa only [Functor.map_comp] using
        (show p.IsHomLift (p.map (f ≫ g))
          (uX ≫ (f ≫ g)) by infer_instance)
    have hcompActual : p.IsHomLift (p.map f ≫ p.map g)
        (categoryPresheafStrictificationFunctorHom P (f ≫ g)).hom := by
      have h := categoryPresheafStrictificationFunctorHom_isHomLift P (f ≫ g)
      rw [p.map_comp] at h
      exact h
    have hcomp : p.IsHomLift (p.map f ≫ p.map g)
        ((categoryPresheafStrictificationFunctorHom P f).hom ≫
          (categoryPresheafStrictificationFunctorHom P g).hom) := by
      exact IsHomLift.comp p (p.map f) (p.map g)
        (categoryPresheafStrictificationFunctorHom P f).hom
        (categoryPresheafStrictificationFunctorHom P g).hom
    have hsource_f : p.IsHomLift (p.map f) (uX ≫ f) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map f) uX f)
    have hsource_g : p.IsHomLift (p.map g) (uY ≫ g) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj Y)) (p.map g) uY g)
    have hfac_fg :
        (categoryPresheafStrictificationFunctorHom P (f ≫ g)).hom ≫ uZ =
          uX ≫ (f ≫ g) := by
      change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        _ _ (p.map (f ≫ g)) (p.map (f ≫ g)) (by simp)
        (uX ≫ (f ≫ g)) hsource_fg) ≫ uZ = _
      simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        (p.obj X) (Functor.Fiber.fiberInclusion.obj
          (P.pullback (𝟙 (p.obj X)) xX))
        (p.map (f ≫ g)) (p.map (f ≫ g)) (by simp)
        (uX ≫ (f ≫ g)) hsource_fg)
    have hfac_f :
        (categoryPresheafStrictificationFunctorHom P f).hom ≫ uY =
          uX ≫ f := by
      change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Y)) uY
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
        _ _ (p.map f) (p.map f) (by simp) (uX ≫ f) hsource_f) ≫ uY = _
      simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Y)) uY
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
        (p.obj X) (Functor.Fiber.fiberInclusion.obj
          (P.pullback (𝟙 (p.obj X)) xX))
        (p.map f) (p.map f) (by simp) (uX ≫ f) hsource_f)
    have hfac_g :
        (categoryPresheafStrictificationFunctorHom P g).hom ≫ uZ =
          uY ≫ g := by
      change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        _ _ (p.map g) (p.map g) (by simp) (uY ≫ g) hsource_g) ≫ uZ = _
      simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        (p.obj Y) (Functor.Fiber.fiberInclusion.obj
          (P.pullback (𝟙 (p.obj Y)) xY))
        (p.map g) (p.map g) (by simp) (uY ≫ g) hsource_g)
    have hEq :
        (categoryPresheafStrictificationFunctorHom P (f ≫ g)).hom ≫ uZ =
          ((categoryPresheafStrictificationFunctorHom P f).hom ≫
            (categoryPresheafStrictificationFunctorHom P g).hom) ≫ uZ := by
      dsimp [xX, xY, xZ, uX, uY, uZ] at hfac_fg hfac_f hfac_g ⊢
      exact hfac_fg.trans <|
        (Category.assoc uX f g).symm.trans <|
          (congrArg (fun k => k ≫ g) hfac_f.symm).trans <|
            (Category.assoc (categoryPresheafStrictificationFunctorHom P f).hom
              uY g).trans <|
              (congrArg (fun k =>
                (categoryPresheafStrictificationFunctorHom P f).hom ≫ k)
                hfac_g.symm).trans <|
                (Category.assoc
                  (categoryPresheafStrictificationFunctorHom P f).hom
                  (categoryPresheafStrictificationFunctorHom P g).hom uZ).symm
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 (p.obj Z)) uZ
      (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
      (p.obj X) (Functor.Fiber.fiberInclusion.obj
        (P.pullback (𝟙 (p.obj X)) xX)) (p.map f ≫ p.map g)
      (categoryPresheafStrictificationFunctorHom P (f ≫ g)).hom
      ((categoryPresheafStrictificationFunctorHom P f).hom ≫
        (categoryPresheafStrictificationFunctorHom P g).hom)
      hcompActual hcomp hEq

theorem categoryPresheafStrictification_exists_equivalence
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :
    ∃ E : S ⥤ CategoryPresheafStrictificationCategory p P,
      IsEquivalenceOverFunctor p
        (categoryPresheafStrictificationProjection P) E ∧
      ∀ x : S,
        E.obj x = categoryPresheafStrictificationObjectOf P x := by
  let E := categoryPresheafStrictificationFunctor P
  let G := categoryPresheafStrictificationInverse P
  refine ⟨E, ?_, ?_⟩
  · refine ⟨G, ?_, ?_, ?_, ?_⟩
    · refine CategoryTheory.Functor.hext (fun x => rfl) ?_
      intro x y f
      let : p.IsHomLift (p.map f)
          (categoryPresheafStrictificationFunctorHom P f).hom :=
        categoryPresheafStrictificationFunctorHom_isHomLift P f
      have hfac := CategoryTheory.IsHomLift.fac p (p.map f)
        (categoryPresheafStrictificationFunctorHom P f).hom
      have hheq := (CategoryTheory.conj_eqToHom_iff_heq'
        (p.map f)
        (p.map (categoryPresheafStrictificationFunctorHom P f).hom)
        (CategoryTheory.IsHomLift.domain_eq p (p.map f)
          (categoryPresheafStrictificationFunctorHom P f).hom).symm
        (CategoryTheory.IsHomLift.codomain_eq p (p.map f)
          (categoryPresheafStrictificationFunctorHom P f).hom)).mp
        (by simpa [Category.assoc] using hfac)
      simpa [E, categoryPresheafStrictificationFunctor,
        categoryPresheafStrictificationProjection,
        categoryPresheafStrictificationHomBase] using hheq.symm
    · refine CategoryTheory.Functor.hext
        (fun A => (categoryPresheafStrictificationPullback A).2) ?_
      intro A B f
      simp [G, categoryPresheafStrictificationInverse,
        categoryPresheafStrictificationProjection,
        categoryPresheafStrictificationHomBase]
    · let comp := E ⋙ G
      let component : ∀ X : S, comp.obj X ≅ X := by
        intro X
        let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
        let uX := P.pullbackMap (𝟙 (p.obj X)) xX
        letI : p.IsStronglyCartesian (𝟙 (p.obj X)) uX :=
          P.pullbackMap_isStronglyCartesian (𝟙 (p.obj X)) xX
        letI : IsIso uX :=
          Functor.IsStronglyCartesian.isIso_of_base_isIso p
            (𝟙 (p.obj X)) uX
        change (P.pullback (𝟙 (p.obj X)) xX).1 ≅ X
        let vX : X ⟶ (P.pullback (𝟙 (p.obj X)) xX).1 :=
          (asIso uX).inv
        refine { hom := uX, inv := vX, hom_inv_id := ?_, inv_hom_id := ?_ }
        · change uX ≫ (asIso uX).inv =
            𝟙 ((P.pullback (𝟙 (p.obj X)) xX).1)
          exact (asIso uX).hom_inv_id
        · change (asIso uX).inv ≫ (asIso uX).hom = 𝟙 (xX.1)
          exact (asIso uX).inv_hom_id
      let e : comp ≅ 𝟭 S :=
        NatIso.ofComponents component (fun {X Y} f => by
          let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
          let xY : Functor.Fiber p (p.obj Y) := ⟨Y, rfl⟩
          let uX := P.pullbackMap (𝟙 (p.obj X)) xX
          let uY := P.pullbackMap (𝟙 (p.obj Y)) xY
          have hfac :
              (categoryPresheafStrictificationFunctorHom P f).hom ≫ uY =
                uX ≫ f := by
            change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
              (𝟙 (p.obj Y)) uY
              (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
              _ _ (p.map f) (p.map f) (by simp) (uX ≫ f) _) ≫ uY = _
            exact Functor.IsStronglyCartesian.fac p (𝟙 (p.obj Y)) uY
              (f' := p.map f) (g := p.map f) (by simp) (uX ≫ f)
          exact hfac)
      refine ⟨e, ?_, ?_⟩
      · refine CategoryTheory.Functor.hext
          (fun X => (categoryPresheafStrictificationPullback
            (categoryPresheafStrictificationObjectOf P X)).2) ?_
        intro X Y f
        let : p.IsHomLift (p.map f)
            (categoryPresheafStrictificationFunctorHom P f).hom :=
          categoryPresheafStrictificationFunctorHom_isHomLift P f
        have hfac := CategoryTheory.IsHomLift.fac p (p.map f)
          (categoryPresheafStrictificationFunctorHom P f).hom
        have hheq := (CategoryTheory.conj_eqToHom_iff_heq'
          (p.map f) (p.map
            (categoryPresheafStrictificationFunctorHom P f).hom)
          (CategoryTheory.IsHomLift.domain_eq p (p.map f)
            (categoryPresheafStrictificationFunctorHom P f).hom).symm
          (CategoryTheory.IsHomLift.codomain_eq p (p.map f)
            (categoryPresheafStrictificationFunctorHom P f).hom)).mp
          (by simpa [Category.assoc] using hfac)
        simpa [G, categoryPresheafStrictificationInverse, E,
          categoryPresheafStrictificationFunctor,
          categoryPresheafStrictificationProjection,
          categoryPresheafStrictificationHomBase] using hheq.symm
      · intro X
        let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
        let eX := (categoryPresheafStrictificationPullback
          (categoryPresheafStrictificationObjectOf P X)).2
        change p.obj (P.pullback (𝟙 (p.obj X)) xX).1 = p.obj X at eX
        let uX := P.pullbackMap (𝟙 (p.obj X)) xX
        change (P.pullback (𝟙 (p.obj X)) xX).1 ⟶ X at uX
        let : p.IsStronglyCartesian (𝟙 (p.obj X)) uX :=
          P.pullbackMap_isStronglyCartesian (𝟙 (p.obj X)) xX
        have hfac := CategoryTheory.IsHomLift.fac p
          (𝟙 (p.obj X)) uX
        have hfac' : 𝟙 (p.obj X) =
            eqToHom eX.symm ≫ p.map uX := by
          simpa [Category.assoc] using hfac
        have hfac'' := congrArg (fun k => eqToHom eX ≫ k) hfac'
        have hbase : p.map uX = eqToHom eX := by
          simpa [Category.assoc] using hfac''.symm
        change p.map uX = eqToHom eX
        exact hbase
    · let comp := G ⋙ E
      let component : ∀ A : CategoryPresheafStrictificationCategory p P,
          comp.obj A ≅ A := by
        intro A
        let xA : Functor.Fiber p
            (p.obj ((categoryPresheafStrictificationPullback A).1)) :=
          ⟨(categoryPresheafStrictificationPullback A).1, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA
        change (P.pullback
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA).1 ⟶
          (categoryPresheafStrictificationPullback A).1 at wA
        letI : p.IsStronglyCartesian
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        letI : IsIso wA :=
          Functor.IsStronglyCartesian.isIso_of_base_isIso p
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA
        dsimp [comp, E, G, categoryPresheafStrictificationFunctor,
          categoryPresheafStrictificationInverse]
        dsimp [xA] at wA ⊢
        let vA : (categoryPresheafStrictificationPullback A).1 ⟶
            (P.pullback
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA).1 :=
          (asIso wA).inv
        let κ : comp.obj A ⟶ A := by
          dsimp [comp, E, G, categoryPresheafStrictificationFunctor,
            categoryPresheafStrictificationInverse]
          exact { hom := wA }
        let κinv : A ⟶ comp.obj A := by
          dsimp [comp, E, G, categoryPresheafStrictificationFunctor,
            categoryPresheafStrictificationInverse]
          exact { hom := vA }
        refine { hom := κ, inv := κinv, hom_inv_id := ?_, inv_hom_id := ?_ }
        · apply categoryPresheafStrictificationHom_ext
          change wA ≫ vA = 𝟙 _
          exact (asIso wA).hom_inv_id
        · apply categoryPresheafStrictificationHom_ext
          change vA ≫ wA = 𝟙 _
          exact (asIso wA).inv_hom_id
      let e : comp ≅
          𝟭 (CategoryPresheafStrictificationCategory p P) :=
        NatIso.ofComponents component (fun {A B} f => by
          let xA : Functor.Fiber p
              (p.obj ((categoryPresheafStrictificationPullback A).1)) :=
            ⟨(categoryPresheafStrictificationPullback A).1, rfl⟩
          let xB : Functor.Fiber p
              (p.obj ((categoryPresheafStrictificationPullback B).1)) :=
            ⟨(categoryPresheafStrictificationPullback B).1, rfl⟩
          let wA := P.pullbackMap
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA
          let wB := P.pullbackMap
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) xB
          let : p.IsStronglyCartesian
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA :=
            P.pullbackMap_isStronglyCartesian _ _
          let : p.IsStronglyCartesian
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB :=
            P.pullbackMap_isStronglyCartesian _ _
          let : p.IsHomLift (p.map f.hom) f.hom := by
            apply CategoryTheory.IsHomLift.of_fac' p
              (p.map f.hom) f.hom rfl rfl
            simp
          have hsource0 : p.IsHomLift
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1)) ≫
                p.map f.hom)
              (wA ≫ f.hom) := by
            exact @CategoryTheory.IsHomLift.comp _ _ _ _ p
              _ _ _ _ _ _
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1)))
              (p.map f.hom) wA f.hom
              (inferInstance : p.IsHomLift
                (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA)
              (inferInstance : p.IsHomLift (p.map f.hom) f.hom)
          have hsource : p.IsHomLift (p.map f.hom) (wA ≫ f.hom) := by
            simpa using hsource0
          let : p.IsHomLift (p.map f.hom) (wA ≫ f.hom) := hsource
          have hfac :
              (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫ wB =
                wA ≫ f.hom := by
            change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB
              (P.pullbackMap_isStronglyCartesian
                (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) xB)
              _ _ (p.map f.hom) (p.map f.hom) (by simp)
              (wA ≫ f.hom) _) ≫ wB = _
            exact Functor.IsStronglyCartesian.fac p
              (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB
              (f' := p.map f.hom) (g := p.map f.hom) (by simp)
              (wA ≫ f.hom)
          dsimp [comp, component, E, G,
            categoryPresheafStrictificationFunctor,
            categoryPresheafStrictificationInverse]
          apply categoryPresheafStrictificationHom_ext
          exact hfac)
      refine ⟨e, ?_, ?_⟩
      · refine CategoryTheory.Functor.hext
          (fun A => (categoryPresheafStrictificationPullback A).2) ?_
        intro A B f
        let xA : Functor.Fiber p
            (p.obj ((categoryPresheafStrictificationPullback A).1)) :=
          ⟨(categoryPresheafStrictificationPullback A).1, rfl⟩
        let xB : Functor.Fiber p
            (p.obj ((categoryPresheafStrictificationPullback B).1)) :=
          ⟨(categoryPresheafStrictificationPullback B).1, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA
        let wB := P.pullbackMap
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) xB
        let eA' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA
        let eB' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB
        let eA0 : p.obj ((categoryPresheafStrictificationPullback A).1) = A.V := by
          exact (categoryPresheafStrictificationPullback A).2
        let eB0 : p.obj ((categoryPresheafStrictificationPullback B).1) = B.V := by
          exact (categoryPresheafStrictificationPullback B).2
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA
          convert h using 1; simp
        have hwB : p.map wB = eqToHom eB' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback B).1))) wB
          convert h using 1; simp
        have hfac :
            (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫ wB =
              wA ≫ f.hom := by
          have h := congrArg (fun k => k.hom) (e.hom.naturality f)
          dsimp [e, NatIso.ofComponents, component, comp] at h
          exact h
        have hfacMap :
            p.map (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫
                p.map wB = p.map wA ≫ p.map f.hom := by
          have h := congrArg p.map hfac
          have h1 := p.map_comp
            (categoryPresheafStrictificationFunctorHom P f.hom).hom wB
          have h2 := p.map_comp wA f.hom
          exact h1.symm.trans (h.trans h2)
        have hmap :
            p.map (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫
                eqToHom eB' = eqToHom eA' ≫ p.map f.hom := by
          have hB := congrArg
            (fun k => p.map
              (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫ k) hwB
          have hA := congrArg (fun k => k ≫ p.map f.hom) hwA
          exact hB.symm.trans (hfacMap.trans hA)
        have hconj :
            (categoryPresheafStrictificationProjection P).map f =
              eqToHom (categoryPresheafStrictificationPullback A).2.symm ≫
                (categoryPresheafStrictificationProjection P).map
                  (categoryPresheafStrictificationFunctorHom P f.hom) ≫
                eqToHom (categoryPresheafStrictificationPullback B).2 := by
          change eqToHom eA0.symm ≫ p.map f.hom ≫ eqToHom eB0 =
            eqToHom eA0.symm ≫
              (eqToHom eA'.symm ≫ p.map
                (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫
                eqToHom eB') ≫ eqToHom eB0
          calc
            eqToHom eA0.symm ≫ p.map f.hom ≫ eqToHom eB0 =
                eqToHom eA0.symm ≫ eqToHom eA'.symm ≫
                  (eqToHom eA' ≫ p.map f.hom) ≫ eqToHom eB0 := by
              simp [Category.assoc]
            _ = eqToHom eA0.symm ≫ eqToHom eA'.symm ≫
                  (p.map
                    (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫
                    eqToHom eB') ≫ eqToHom eB0 := by
              have hstep := congrArg
                (fun k => eqToHom eA0.symm ≫ eqToHom eA'.symm ≫ k ≫
                  eqToHom eB0) hmap
              exact hstep.symm
            _ = eqToHom eA0.symm ≫
                  (eqToHom eA'.symm ≫ p.map
                    (categoryPresheafStrictificationFunctorHom P f.hom).hom ≫
                    eqToHom eB') ≫ eqToHom eB0 := by
              simp [Category.assoc]
        have hheq := (CategoryTheory.conj_eqToHom_iff_heq'
            ((categoryPresheafStrictificationProjection P).map f)
            ((categoryPresheafStrictificationProjection P).map
              (categoryPresheafStrictificationFunctorHom P f.hom))
            (categoryPresheafStrictificationPullback A).2.symm
            (categoryPresheafStrictificationPullback B).2).mp hconj
        simpa [G, E, categoryPresheafStrictificationFunctor,
          categoryPresheafStrictificationInverse,
          categoryPresheafStrictificationProjection,
          categoryPresheafStrictificationHomBase] using hheq.symm
      · intro A
        let xA : Functor.Fiber p
            (p.obj ((categoryPresheafStrictificationPullback A).1)) :=
          ⟨(categoryPresheafStrictificationPullback A).1, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) xA
        let eA' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA
        let eA0 : p.obj ((categoryPresheafStrictificationPullback A).1) = A.V := by
          exact (categoryPresheafStrictificationPullback A).2
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((categoryPresheafStrictificationPullback A).1))) wA
          convert h using 1; simp
        dsimp [e, NatIso.ofComponents, component, comp, G, E,
          categoryPresheafStrictificationFunctor,
          categoryPresheafStrictificationInverse,
          categoryPresheafStrictificationProjection,
          categoryPresheafStrictificationHomBase]
        change eqToHom eA'.symm ≫ p.map wA ≫ eqToHom eA0 =
          eqToHom eA0
        rw [hwA]
        simp
  · intro x
    rfl

theorem fibredCategory_isEquivalentTo_split
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] :
    ∃ F : CategoryPresheaf C,
      ∃ h : S ⥤ categoryPresheafCategory F,
        IsEquivalenceOverFunctor p (categoryPresheafProjection F) h := by
  sorry

/-! ## Presheaves of groupoids -/

structure GroupoidPresheaf
    (C : Type u') [Category.{v'} C] where
  value : CategoryPresheaf C
  fibre_is_groupoid : ∀ U : C,
    IsGroupoid (value.obj ⟨Opposite.op U⟩)

abbrev groupoidPresheafCategory
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) :=
  categoryPresheafCategory F.value

abbrev groupoidPresheafProjection
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) :
    groupoidPresheafCategory F ⥤ C :=
  categoryPresheafProjection F.value

abbrev groupoidPresheafRestriction
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) {V U : C} (f : V ⟶ U) :
    F.value.obj ⟨Opposite.op U⟩ ⥤ F.value.obj ⟨Opposite.op V⟩ :=
  categoryPresheafRestriction F.value f

theorem groupoidPresheafRestriction_comp
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    Nonempty (groupoidPresheafRestriction F (g ≫ f) ≅
      groupoidPresheafRestriction F f ⋙ groupoidPresheafRestriction F g) := by
  exact categoryPresheafRestriction_comp F.value g f

theorem groupoidPresheaf_fibre_is_groupoid
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) (U : C) :
    IsGroupoid (Functor.Fiber (groupoidPresheafProjection F) U) := by
  sorry

theorem groupoidPresheafProjection_isFibredInGroupoids
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) :
    (groupoidPresheafProjection F).IsFibredInGroupoids := by
  apply (fibredInGroupoids_iff_fibred_groupoid_fibres
    (groupoidPresheafProjection F)).mpr
  exact ⟨groupoidPresheaf_fibre_is_groupoid F,
    categoryPresheafProjection_isFibered F.value⟩

theorem groupoidPresheaf_exists_lift
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C) {V U : C} (f : V ⟶ U)
    (x : F.value.obj ⟨op U⟩) :
    ∃ y : groupoidPresheafCategory F,
      ∃ φ : y ⟶ (⟨U, x⟩ : groupoidPresheafCategory F),
        (groupoidPresheafProjection F).IsHomLift f φ := by
  exact ⟨categoryPresheafCartesianDomain F.value f x,
    categoryPresheafCartesianLift F.value f x,
    categoryPresheafCartesianLift_isHomLift F.value f x⟩

theorem groupoidPresheaf_unique_lift
    {C : Type u'} [Category.{v'} C]
    (F : GroupoidPresheaf C)
    {x y z : groupoidPresheafCategory F} (φ : y ⟶ x) (ψ : z ⟶ x)
    {f : (groupoidPresheafProjection F).obj z ⟶
      (groupoidPresheafProjection F).obj y}
    (h : f ≫ (groupoidPresheafProjection F).map φ =
      (groupoidPresheafProjection F).map ψ) :
    ∃! χ : z ⟶ y,
      (groupoidPresheafProjection F).IsHomLift f χ ∧ χ ≫ φ = ψ := by
  exact (groupoidPresheafProjection_isFibredInGroupoids F).unique_lift
    φ ψ h

def IsSplitCategoryFibredInGroupoids
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) : Prop :=
  p.IsFibredInGroupoids ∧
    ∃ F : GroupoidPresheaf C,
      IsomorphicOverBase p (groupoidPresheafProjection F)

theorem groupoidPresheafProjection_isSplit
    {C : Type u'} [Category.{v'} C] (F : GroupoidPresheaf C) :
    IsSplitCategoryFibredInGroupoids
      (groupoidPresheafProjection F) := by
  constructor
  · exact groupoidPresheafProjection_isFibredInGroupoids F
  · exact ⟨F, 𝟭 _, 𝟭 _, Functor.id_comp _, Functor.id_comp _,
      Functor.id_comp _, Functor.id_comp _⟩

theorem fibredInGroupoids_isEquivalentTo_split
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibredInGroupoids] :
    ∃ F : GroupoidPresheaf C,
      ∃ h : S ⥤ groupoidPresheafCategory F,
        IsEquivalenceOverFunctor p (groupoidPresheafProjection F) h := by
  sorry

end
