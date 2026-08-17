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
  sorry

/-! ## Examples -/

theorem groupHomomorphism_fibredInGroupoids_iff_surjective
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    (MonoidHom.toFunctor p).IsFibredInGroupoids ↔ Function.Surjective p := by
  sorry

theorem groupHomomorphism_fibre_is_kernel_groupoid
    {G H : Type*} [Group G] [Group H] (p : G →* H) :
    Nonempty
      (Functor.Fiber (MonoidHom.toFunctor p) (SingleObj.star H) ≌
        SingleObj (MonoidHom.ker p)) := by
  sorry

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

theorem categoriesFibredInGroupoids_have_twoFibreProducts
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (hX : IsGroupoidFibredCategoryOver X)
    (hY : IsGroupoidFibredCategoryOver Y)
    (hS : IsGroupoidFibredCategoryOver S)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredInGroupoidsTwoFibreProduct F G) := by
  sorry

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
  sorry

theorem fibredInGroupoids_fullyFaithful_iff_fibrewise
    {S S' C : Type*} [Category* S] [Category* S'] [Category* C]
    (p : S ⥤ C) (p' : S' ⥤ C) (G : S ⥤ S')
    (over : G ⋙ p' = p)
    (hp : p.IsFibredInGroupoids) (hp' : p'.IsFibredInGroupoids) :
    Nonempty G.FullyFaithful ↔
      ∀ U : C, Nonempty (fibreFunctor p p' G over U).FullyFaithful := by
  sorry

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
        fibredOverNatTransComp (fibredWhiskerRight η ψ)
          (fibredWhiskerRight θ ψ) by
      apply OverNatTrans.ext
      exact congrArg (fun q => q.toNatTrans)
        (Bicategory.comp_whiskerRight (B := FibredCategoryOver C)
          η θ ψ)]
    rfl

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
  sorry

theorem fibredInGroupoids_over_slice
    {S C : Type*} [Category* S] [Category* C]
    (U : C) (p : S ⥤ C) (p' : S ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p)
    (hp : p.IsFibredInGroupoids) :
    p'.IsFibredInGroupoids := by
  sorry

theorem fibredInGroupoids_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C)
    (hp : p.IsFibredInGroupoids) (hq : q.IsFibredInGroupoids) :
    (p ⋙ q).IsFibredInGroupoids := by
  sorry

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
  sorry

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
