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
      let _ : IsIso f := by
        exact hH.isIso_of_isIso_map f
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
    let P : FibredInGroupoidsTwoFibreProduct F F := {
      product := canonicalFibredTwoFibreProduct X X Y F F
      fibres_are_groupoids :=
        canonicalFibredTwoFibreProduct_fibres_are_groupoids
          X X Y hX hX hY F F }
    have hpT : pT.IsFibredInGroupoids := by
      simpa [P, pT, canonicalFibredTwoFibreProduct_diagram] using
        fibredInGroupoidsTwoFibreProduct_apex_isFibredInGroupoids P
    have hDfibre : ∀ U : C,
        (fibreFunctor pX pT D rfl U).IsEquivalence := by
      intro U
      exact (fibredInGroupoids_equivalence_iff_fibrewise
        pX pT D rfl (groupoidFibredCategoryOver_isFibredInGroupoids X hX)
          hpT).mp hD U
    /- Prior attempt: the diagonal fibrewise equivalences above do not provide
       a `(overFunctor F.underlying).Full` instance for this constructor. -/
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
    (prePostcompositionFunctor φ ψ).IsEquivalence := by
  sorry

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
  sorry

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

end
