import Formalization.Books.Categories.Unit32.CategoriesOverCategories
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Categories, Chapter 33: Fibred categories

The source uses the universal-property definition of a strongly cartesian
morphism.  Mathlib has that definition, its factorisation API, and the
equivalent `IsFibered` interface already in
`CategoryTheory.FiberedCategory`; this file keeps those declarations as the
mathematical primitives.  The records below package the extra source-facing
data (chosen pullbacks, morphisms over a fixed base, and the final
factorisation statement).
-/

namespace Formalization.Books.Categories.Unit33

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit30
open Formalization.Books.Categories.Unit31
open Formalization.Books.Categories.Unit32

universe u₁ v₁ u₂ v₂ w v u

noncomputable section

/-! ## Strongly cartesian morphisms -/

theorem fibred_category_iff_exists_stronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C) :
    p.IsFibered ↔
      ∀ (x : X) (R : C) (f : R ⟶ p.obj x),
        ∃ (y : X) (φ : y ⟶ x), Functor.IsStronglyCartesian p f φ := by
  constructor
  · intro hp x R f
    obtain ⟨y, φ, hφ⟩ := hp.toIsPreFibered.exists_isCartesian' f
    exact ⟨y, φ, @Functor.IsFibered.isStronglyCartesian_of_isCartesian
      _ _ _ _ p hp _ _ f _ _ φ hφ⟩
  · exact Functor.IsFibered.of_exists_isStronglyCartesian

theorem stronglyCartesian_comp
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S T : C} {a b c : X} {f : R ⟶ S} {g : S ⟶ T}
    {φ : a ⟶ b} {ψ : b ⟶ c}
    [Functor.IsStronglyCartesian p f φ]
    [Functor.IsStronglyCartesian p g ψ] :
    Functor.IsStronglyCartesian p (f ≫ g) (φ ≫ ψ) := by
  infer_instance

theorem iso_is_stronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S : C} {a b : X} (f : R ⟶ S) (e : a ≅ b)
    [p.IsHomLift f e.hom] :
    Functor.IsStronglyCartesian p f e.hom := by
  infer_instance

theorem stronglyCartesian_of_base_isIso
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S : C} {a b : X} (f : R ⟶ S) (φ : a ⟶ b)
    [Functor.IsStronglyCartesian p f φ] [IsIso f] :
    IsIso φ := by
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p f φ

theorem stronglyCartesian_over_composition
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [Functor.IsStronglyCartesian F (F.map φ) φ]
    [Functor.IsStronglyCartesian G (G.map (F.map φ)) (F.map φ)] :
    Functor.IsStronglyCartesian (F ⋙ G) ((F ⋙ G).map φ) φ := by
  constructor
  intro c g τ hτ
  let : (F ⋙ G).IsHomLift (g ≫ (F ⋙ G).map φ) τ := hτ
  have hcomp : G.map (F.map τ) = g ≫ G.map (F.map φ) := by
    symm
    simpa only [Functor.comp_map] using
      (CategoryTheory.IsHomLift.eq_of_isHomLift
        (F ⋙ G) (g ≫ (F ⋙ G).map φ) τ)
  obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property G
      (G.map (F.map φ)) (F.map φ) g (G.map (F.map τ)) hcomp (F.map τ)
  obtain ⟨δ, ⟨hδ, hδeq⟩, hδuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property F
      (F.map φ) φ χ (F.map τ) hχeq.symm τ
  have hδmap : χ = F.map δ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift F χ δ
  have hχmap : g = G.map χ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift G g χ
  have hmap : g = (F ⋙ G).map δ := by
    calc
      g = G.map χ := hχmap
      _ = G.map (F.map δ) := congrArg G.map hδmap
      _ = (F ⋙ G).map δ := by simp only [Functor.comp_map]
  have : (F ⋙ G).IsHomLift g δ := by
    rw [hmap]
    infer_instance
  refine ⟨δ, ⟨inferInstance, hδeq⟩, ?_⟩
  intro δ' ⟨hδ'base, hδ'eq⟩
  have hδ'comp : g = G.map (F.map δ') :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (F ⋙ G) g δ'
  let : G.IsHomLift g (F.map δ') := by
    rw [hδ'comp]
    infer_instance
  have hFδ' : F.map δ' = χ :=
    hχuniq (F.map δ') ⟨inferInstance, by
      simpa [Functor.comp_map] using congrArg F.map hδ'eq⟩
  let : F.IsHomLift χ δ' := by
    rw [← hFδ']
    infer_instance
  exact hδuniq δ' ⟨inferInstance, hδ'eq⟩

theorem stronglyCartesian_fibre_product
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) {x y z : X} (f : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map f) f]
    {P : C} {π₁ : P ⟶ p.obj x} {π₂ : P ⟶ p.obj z}
    (hP : IsPullback π₁ π₂ (p.map f) (p.map g))
    (w : X) (a : w ⟶ z)
    [Functor.IsStronglyCartesian p π₂ a] :
    ∃ b : w ⟶ x, IsPullback b a f g := by
  have h₀ : p.obj w = P := IsHomLift.domain_eq p π₂ a
  cases h₀
  let : p.IsHomLift (π₁ ≫ p.map f) (a ≫ g) := by
    rw [hP.w]
    infer_instance
  let b : w ⟶ x :=
    Functor.IsStronglyCartesian.map p (p.map f) f
      (f' := π₁ ≫ p.map f) (g := π₁) rfl (a ≫ g)
  have hb : b ≫ f = a ≫ g := by
    dsimp [b]
    simp
  have : p.IsHomLift π₁ b := by
    dsimp [b]
    infer_instance
  have hbbase : π₁ = p.map b :=
    CategoryTheory.IsHomLift.eq_of_isHomLift p π₁ b
  have habase : π₂ = p.map a :=
    CategoryTheory.IsHomLift.eq_of_isHomLift p π₂ a
  refine ⟨b, ?_⟩
  apply IsPullback.mk' hb
  · intro T u v hu hv
    have h₁ : p.map u ≫ π₁ = p.map v ≫ π₁ := by
      simpa only [Functor.map_comp, hbbase.symm] using congrArg p.map hu
    have h₂ : p.map u ≫ π₂ = p.map v ≫ π₂ := by
      simpa only [Functor.map_comp, habase.symm] using congrArg p.map hv
    have huv : p.map u = p.map v := hP.hom_ext h₁ h₂
    let : p.IsHomLift (p.map u) v := by
      rw [huv]
      infer_instance
    exact Functor.IsStronglyCartesian.ext p π₂ a (p.map u) hv
  · intro T r s hrs
    let k : p.obj T ⟶ p.obj w :=
      hP.lift (p.map r) (p.map s) (by
        simpa only [← Functor.map_comp] using congrArg p.map hrs)
    have hk₁ : k ≫ π₁ = p.map r := by
      dsimp [k]
      simp
    have hk₂ : k ≫ π₂ = p.map s := by
      dsimp [k]
      simp
    let : p.IsHomLift (k ≫ π₂) s := by
      rw [hk₂]
      infer_instance
    obtain ⟨t, ⟨ht, hta⟩, _⟩ :=
      Functor.IsStronglyCartesian.universal_property p π₂ a k
        (p.map s) hk₂.symm s
    let := ht
    have htb : t ≫ b = r := by
      have hcomp : (t ≫ b) ≫ f = r ≫ f := by
        calc
          (t ≫ b) ≫ f = t ≫ (b ≫ f) := by simp [Category.assoc]
          _ = t ≫ (a ≫ g) := by rw [hb]
          _ = (t ≫ a) ≫ g := by simp [Category.assoc]
          _ = s ≫ g := by rw [hta]
          _ = r ≫ f := hrs.symm
      have : p.IsHomLift (k ≫ π₁) (t ≫ b) := by
        infer_instance
      let : p.IsHomLift (k ≫ π₁) r := by
        rw [hk₁]
        infer_instance
      exact Functor.IsStronglyCartesian.ext p (p.map f) f (k ≫ π₁) hcomp
    exact ⟨t, htb, hta⟩

/-! ## Pullbacks in a fibred category -/

/- A choice of pullbacks is a choice of a strongly cartesian lift for every
   object in every fibre.  `Functor.Fiber` is Mathlib's canonical fibre
   category, so no second fibre-category construction is introduced here. -/
structure PullbackChoice
    {X : Type u₁} {C : Type u₂} [Category.{v₁} X] [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] where
  pullback : ∀ {R S : C} (_f : R ⟶ S) (_x : Functor.Fiber p S),
    Functor.Fiber p R
  pullbackMap : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
    (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).obj (pullback f x) ⟶ x.1
  pullbackMap_isStronglyCartesian : ∀ {R S : C} (f : R ⟶ S)
    (x : Functor.Fiber p S),
    Functor.IsStronglyCartesian p f (pullbackMap f x)

attribute [instance] PullbackChoice.pullbackMap_isStronglyCartesian

namespace PullbackChoice

variable {X : Type u₁} {C : Type u₂} [Category.{v₁} X] [Category.{v₂} C]
variable {p : X ⥤ C} [p.IsFibered]

/- Mathlib's chosen Cartesian lift is converted to a strongly Cartesian lift
   using the canonical `IsFibered` instance. -/
noncomputable def default (p : X ⥤ C) [p.IsFibered] : PullbackChoice p where
  pullback f x := Functor.Fiber.mk (Functor.IsPreFibered.pullbackObj_proj (p := p) x.2 f)
  pullbackMap f x := Functor.IsPreFibered.pullbackMap (p := p) x.2 f
  pullbackMap_isStronglyCartesian f x := by
    exact @Functor.IsFibered.isStronglyCartesian_of_isCartesian
      _ _ _ _ p inferInstance _ _ f _ _
      (Functor.IsPreFibered.pullbackMap (p := p) x.2 f)
      (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 f)

theorem exists_choice (p : X ⥤ C) [p.IsFibered] : Nonempty (PullbackChoice p) :=
  ⟨default p⟩

def pullbackFunctor (P : PullbackChoice p) {R S : C} (f : R ⟶ S) :
    Functor.Fiber p S ⥤ Functor.Fiber p R where
  obj x := P.pullback f x
  map {x y} φ := by
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f y) :=
      P.pullbackMap_isStronglyCartesian f y
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f x) :=
      P.pullbackMap_isStronglyCartesian f x
    haveI : p.IsHomLift (𝟙 S) φ.1 := φ.2
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ φ.1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S φ.1
    have hf : f = 𝟙 R ≫ f := by simp
    refine ⟨@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
      (P.pullbackMap f y) _ _ _ (𝟙 R) f hf (P.pullbackMap f x ≫ φ.1)
      hφ', ?_⟩
    exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ f
      (P.pullbackMap f y) _ _ _ (𝟙 R) f hf (P.pullbackMap f x ≫ φ.1)
      hφ'
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    have : p.IsHomLift (𝟙 S) (𝟙 x.1) := IsHomLift.id x.2
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ (𝟙 x.1)) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S (𝟙 x.1)
    let : p.IsHomLift f (P.pullbackMap f x ≫ (𝟙 x.1)) := hφ'
    have hpull : p.obj (Functor.Fiber.fiberInclusion.obj (P.pullback f x)) = R :=
      (P.pullback f x).2
    change
      Functor.IsStronglyCartesian.map p f (P.pullbackMap f x)
          (f' := f) (g := 𝟙 R) (by simp)
          (P.pullbackMap f x ≫ (𝟙 x.1)) =
        𝟙 ((P.pullback f x).1)
    let : p.IsHomLift (𝟙 R) (𝟙 ((P.pullback f x).1)) :=
      IsHomLift.id hpull
    symm
    exact @Functor.IsStronglyCartesian.map_uniq _ _ _ _ p R S
      (P.pullback f x).1 x.1 f (P.pullbackMap f x)
      (P.pullbackMap_isStronglyCartesian f x)
      R (P.pullback f x).1 (𝟙 R) f (by simp)
      (P.pullbackMap f x ≫ (𝟙 x.1)) hφ'
      (𝟙 ((P.pullback f x).1)) (IsHomLift.id hpull) (by
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
  map_comp := by
    intro x y z φ ψ
    apply Functor.Fiber.hom_ext
    let : Functor.IsStronglyCartesian p f (P.pullbackMap f y) :=
      P.pullbackMap_isStronglyCartesian f y
    let : Functor.IsStronglyCartesian p f (P.pullbackMap f z) :=
      P.pullbackMap_isStronglyCartesian f z
    have : p.IsHomLift (𝟙 S) φ.1 := φ.2
    have : p.IsHomLift (𝟙 S) ψ.1 := ψ.2
    have : p.IsHomLift (𝟙 S) (φ ≫ ψ).1 := (φ ≫ ψ).2
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ φ.1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S φ.1
    have hψ' : p.IsHomLift f (P.pullbackMap f y ≫ ψ.1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f y) S ψ.1
    have hcomp' : p.IsHomLift f (P.pullbackMap f x ≫ (φ ≫ ψ).1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S (φ ≫ ψ).1
    let mφ : (P.pullback f x).1 ⟶ (P.pullback f y).1 :=
      @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f y) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f x ≫ φ.1) hφ'
    let mψ : (P.pullback f y).1 ⟶ (P.pullback f z).1 :=
      @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f z) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f y ≫ ψ.1) hψ'
    let mcomp : (P.pullback f x).1 ⟶ (P.pullback f z).1 :=
      @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f z) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f x ≫ (φ ≫ ψ).1) hcomp'
    have hmφ : p.IsHomLift (𝟙 R) mφ := by
      dsimp [mφ]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f y) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f x ≫ φ.1) hφ'
    have hmψ : p.IsHomLift (𝟙 R) mψ := by
      dsimp [mψ]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f z) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f y ≫ ψ.1) hψ'
    let : p.IsHomLift (𝟙 R) mφ := hmφ
    let : p.IsHomLift (𝟙 R) mψ := hmψ
    have hmcomp : p.IsHomLift (𝟙 R) (mφ ≫ mψ) := by infer_instance
    change mcomp = mφ ≫ mψ
    let : p.IsHomLift (𝟙 R) (mφ ≫ mψ) := hmcomp
    symm
    exact (@Functor.IsStronglyCartesian.map_uniq _ _ _ _ p R S
      (P.pullback f z).1 z.1 f (P.pullbackMap f z)
      (P.pullbackMap_isStronglyCartesian f z)
      R (P.pullback f x).1 (𝟙 R) f (by simp)
      (P.pullbackMap f x ≫ (φ ≫ ψ).1)
      hcomp'
      (mφ ≫ mψ)
      hmcomp
      (by
        have hfacφ : mφ ≫ P.pullbackMap f y =
            P.pullbackMap f x ≫ φ.1 := by
          dsimp [mφ]
          exact Functor.IsStronglyCartesian.fac p f (P.pullbackMap f y)
            (f' := f) (g := 𝟙 R) (by simp)
            (P.pullbackMap f x ≫ φ.1)
        have hfacψ : mψ ≫ P.pullbackMap f z =
            P.pullbackMap f y ≫ ψ.1 := by
          dsimp [mψ]
          exact Functor.IsStronglyCartesian.fac p f (P.pullbackMap f z)
            (f' := f) (g := 𝟙 R) (by simp)
            (P.pullbackMap f y ≫ ψ.1)
        have h₁ := Category.assoc mφ mψ (P.pullbackMap f z)
        have h₂ := congrArg (fun k => mφ ≫ k) hfacψ
        have h₃ := (Category.assoc mφ (P.pullbackMap f y) ψ.1).symm
        have h₄ := congrArg (fun k => k ≫ ψ.1) hfacφ
        have h₅ := Category.assoc (P.pullbackMap f x) φ.1 ψ.1
        exact h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅)))))

def IsUnital (P : PullbackChoice p) : Prop :=
  ∀ (U : C) (x : Functor.Fiber p U), P.pullback (𝟙 U) x = x

theorem exists_unital (p : X ⥤ C) [p.IsFibered] :
    ∃ P : PullbackChoice p, P.IsUnital := by
  classical
  let P₀ := default p
  let pb : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
      Functor.Fiber p R := fun {R S} f x => by
    by_cases hRS : R = S
    · subst R
      by_cases hf : f = 𝟙 S
      · simpa [hf]
      · exact P₀.pullback f x
    · exact P₀.pullback f x
  have hpb (U : C) (x : Functor.Fiber p U) : pb (𝟙 U) x = x := by
    dsimp [pb]
    simp
  let pbm : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
      (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).obj (pb f x) ⟶ x.1 := by
    intro R S f x
    by_cases hRS : R = S
    · subst R
      by_cases hf : f = 𝟙 S
      · subst f
        exact Functor.Fiber.fiberInclusion.map (eqToHom (hpb S x))
      · have hpb₀ : pb f x = P₀.pullback f x := by
          dsimp [pb]
          simp [hf]
        exact Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
          P₀.pullbackMap f x
    · have hpb₀ : pb f x = P₀.pullback f x := by
        dsimp [pb]
        simp [hRS]
      exact Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
        P₀.pullbackMap f x
  have hfiberIsoStrong : ∀ {U : C} {a b : Functor.Fiber p U} (h : a = b),
      p.IsStronglyCartesian (𝟙 U)
        ((Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ X).map (eqToHom h)) := by
    intro U a b h
    let e : a ≅ b := eqToIso h
    let eX := (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ X).mapIso e
    let : p.IsHomLift (𝟙 U) eX.hom := by
      dsimp [eX, e]
      infer_instance
    simpa [eX, e] using iso_is_stronglyCartesian p (𝟙 U) eX
  let P : PullbackChoice p :=
    { pullback := pb
      pullbackMap := pbm
      pullbackMap_isStronglyCartesian := by
        intro R S f x
        by_cases hRS : R = S
        · subst R
          by_cases hf : f = 𝟙 S
          · subst f
            have hpbm : pbm (𝟙 S) x =
                Functor.Fiber.fiberInclusion.map (eqToHom (hpb S x)) := by
              have hx := hpb S x
              dsimp [pbm]
              simp
              congr 1
            rw [hpbm]
            exact hfiberIsoStrong (hpb S x)
          · have hpb₀ : pb f x = P₀.pullback f x := by
              dsimp [pb]
              simp [hf]
            have hpbm : pbm f x =
                Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
                  P₀.pullbackMap f x := by
              dsimp [pbm]
              simp [pb, hf]
            rw [hpbm]
            let : p.IsStronglyCartesian (𝟙 S)
                (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀)) :=
              hfiberIsoStrong hpb₀
            let : p.IsStronglyCartesian f (P₀.pullbackMap f x) :=
              P₀.pullbackMap_isStronglyCartesian f x
            simpa using
              (show p.IsStronglyCartesian (𝟙 S ≫ f)
                (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
                  P₀.pullbackMap f x) by infer_instance)
        · have hpb₀ : pb f x = P₀.pullback f x := by
            dsimp [pb]
            simp [hRS]
          have hpbm : pbm f x =
              Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
                P₀.pullbackMap f x := by
            dsimp [pbm]
            simp [pb, hRS]
          rw [hpbm]
          let : p.IsStronglyCartesian (𝟙 R)
              (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀)) :=
            hfiberIsoStrong hpb₀
          let : p.IsStronglyCartesian f (P₀.pullbackMap f x) :=
            P₀.pullbackMap_isStronglyCartesian f x
          simpa using
            (show p.IsStronglyCartesian (𝟙 R ≫ f)
              (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀) ≫
                P₀.pullbackMap f x) by infer_instance) }
  refine ⟨P, ?_⟩
  intro U x
  exact hpb U x

end PullbackChoice

theorem pullback_composition_iso
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p)
    {R S T : C} (f : R ⟶ S) (g : S ⟶ T) :
    ∃! α : P.pullbackFunctor (f ≫ g) ≅
        P.pullbackFunctor g ⋙ P.pullbackFunctor f,
      ∀ x : Functor.Fiber p T,
        Functor.Fiber.fiberInclusion.map (α.hom.app x) ≫
            P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x =
          P.pullbackMap (f ≫ g) x := by
  have pullbackMap_fac {A B : C} (h : A ⟶ B)
      {x y : Functor.Fiber p B} (φ : x ⟶ y) :
      ((P.pullbackFunctor h).map φ).1 ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1 := by
    let : p.IsHomLift (𝟙 B) φ.1 := φ.2
    let : p.IsStronglyCartesian h (P.pullbackMap h y) :=
      P.pullbackMap_isStronglyCartesian h y
    let : p.IsStronglyCartesian h (P.pullbackMap h x) :=
      P.pullbackMap_isStronglyCartesian h x
    have hφ' : p.IsHomLift h (P.pullbackMap h x ≫ φ.1) := by
      exact IsHomLift.comp_lift_id_right' p h (P.pullbackMap h x) B φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ h
        (P.pullbackMap h y) _ _ _ (𝟙 A) h (by simp)
        (P.pullbackMap h x ≫ φ.1) hφ') ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac p h (P.pullbackMap h y)
      (f' := h) (g := 𝟙 A) (by simp) (P.pullbackMap h x ≫ φ.1)
  let component : ∀ x : Functor.Fiber p T,
      P.pullback (f ≫ g) x ≅ P.pullback f (P.pullback g x) := by
    intro x
    letI : p.IsStronglyCartesian f (P.pullbackMap f (P.pullback g x)) :=
      P.pullbackMap_isStronglyCartesian f (P.pullback g x)
    letI : p.IsStronglyCartesian g (P.pullbackMap g x) :=
      P.pullbackMap_isStronglyCartesian g x
    letI : p.IsStronglyCartesian (f ≫ g)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) := by
      exact @Functor.IsStronglyCartesian.comp _ _ _ _ p R S T _ _ _ f g _ _
        (P.pullbackMap_isStronglyCartesian f (P.pullback g x))
        (P.pullbackMap_isStronglyCartesian g x)
    let hom := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (f ≫ g)
      (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) _ _ _ (𝟙 R) (f ≫ g) (by simp)
      (P.pullbackMap (f ≫ g) x) (by infer_instance)
    let inv := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (f ≫ g)
      (P.pullbackMap (f ≫ g) x) _ _ _ (𝟙 R) (f ≫ g) (by simp)
      (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) (by infer_instance)
    have hhom : hom ≫ P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x =
        P.pullbackMap (f ≫ g) x := by
      dsimp [hom]
      exact Functor.IsStronglyCartesian.fac p (f ≫ g)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x)
        (f' := f ≫ g) (g := 𝟙 R) (by simp) (P.pullbackMap (f ≫ g) x)
    have hinv : inv ≫ P.pullbackMap (f ≫ g) x =
        P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x := by
      dsimp [inv]
      exact Functor.IsStronglyCartesian.fac p (f ≫ g)
        (P.pullbackMap (f ≫ g) x)
        (f' := f ≫ g) (g := 𝟙 R) (by simp)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x)
    have hhomLift : p.IsHomLift (𝟙 R) hom := by
      dsimp [hom]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ (f ≫ g)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) _ _ _
        (𝟙 R) (f ≫ g) (by simp) (P.pullbackMap (f ≫ g) x) (by infer_instance)
    have hinvLift : p.IsHomLift (𝟙 R) inv := by
      dsimp [inv]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _ (f ≫ g)
        (P.pullbackMap (f ≫ g) x) _ _ _ (𝟙 R) (f ≫ g) (by simp)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) (by infer_instance)
    letI : p.IsHomLift (𝟙 R) hom := hhomLift
    letI : p.IsHomLift (𝟙 R) inv := hinvLift
    let homF : P.pullback (f ≫ g) x ⟶ P.pullback f (P.pullback g x) :=
      ⟨hom, hhomLift⟩
    let invF : P.pullback f (P.pullback g x) ⟶ P.pullback (f ≫ g) x :=
      ⟨inv, hinvLift⟩
    refine { hom := homF, inv := invF, hom_inv_id := ?_, inv_hom_id := ?_ }
    · apply Functor.Fiber.hom_ext
      change hom ≫ inv = 𝟙 _
      let : p.IsHomLift (𝟙 R) (hom ≫ inv) := by infer_instance
      let : p.IsHomLift (𝟙 R)
          (𝟙 (Functor.Fiber.fiberInclusion.obj (P.pullback (f ≫ g) x))) := by
        have hx : p.obj (Functor.Fiber.fiberInclusion.obj (P.pullback (f ≫ g) x)) = R :=
          (P.pullback (f ≫ g) x).2
        exact IsHomLift.id hx
      apply Functor.IsStronglyCartesian.ext p (f ≫ g)
        (P.pullbackMap (f ≫ g) x) (𝟙 R)
      calc
        (hom ≫ inv) ≫ P.pullbackMap (f ≫ g) x =
            hom ≫ (inv ≫ P.pullbackMap (f ≫ g) x) := by simp [Category.assoc]
        _ = hom ≫ (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) :=
          by rw [hinv]
        _ = P.pullbackMap (f ≫ g) x := hhom
        _ = (𝟙 _ : _ ⟶ _) ≫ P.pullbackMap (f ≫ g) x := by simp
    · apply Functor.Fiber.hom_ext
      change inv ≫ hom = 𝟙 _
      let : p.IsHomLift (𝟙 R) (inv ≫ hom) := by infer_instance
      let : p.IsHomLift (𝟙 R)
          (𝟙 (Functor.Fiber.fiberInclusion.obj
            (P.pullback f (P.pullback g x)))) := by
        have hx : p.obj (Functor.Fiber.fiberInclusion.obj
            (P.pullback f (P.pullback g x))) = R :=
          (P.pullback f (P.pullback g x)).2
        exact IsHomLift.id hx
      apply Functor.IsStronglyCartesian.ext p (f ≫ g)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) (𝟙 R)
      calc
        (inv ≫ hom) ≫
            (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) =
            inv ≫ (hom ≫
              (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x)) := by
                simp [Category.assoc]
        _ = inv ≫ P.pullbackMap (f ≫ g) x := by rw [hhom]
        _ = P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x := hinv
        _ = (𝟙 _ : _ ⟶ _) ≫
            (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) := by simp
  have component_fac (z : Functor.Fiber p T) :
      (component z).hom.1 ≫ P.pullbackMap f (P.pullback g z) ≫
          P.pullbackMap g z = P.pullbackMap (f ≫ g) z := by
    let : p.IsStronglyCartesian f (P.pullbackMap f (P.pullback g z)) :=
      P.pullbackMap_isStronglyCartesian f (P.pullback g z)
    let : p.IsStronglyCartesian g (P.pullbackMap g z) :=
      P.pullbackMap_isStronglyCartesian g z
    let : p.IsStronglyCartesian (f ≫ g)
        (P.pullbackMap f (P.pullback g z) ≫ P.pullbackMap g z) := by
      exact @Functor.IsStronglyCartesian.comp _ _ _ _ p R S T _ _ _ f g _ _
        (P.pullbackMap_isStronglyCartesian f (P.pullback g z))
        (P.pullbackMap_isStronglyCartesian g z)
    dsimp [component]
    exact Functor.IsStronglyCartesian.fac p (f ≫ g)
      (P.pullbackMap f (P.pullback g z) ≫ P.pullbackMap g z)
        (f' := f ≫ g) (g := 𝟙 R) (by simp)
        (P.pullbackMap (f ≫ g) z)
  let α : P.pullbackFunctor (f ≫ g) ≅
      P.pullbackFunctor g ⋙ P.pullbackFunctor f :=
    NatIso.ofComponents component (by
      intro x y φ
      apply Functor.Fiber.hom_ext
      let mfg := (P.pullbackFunctor (f ≫ g)).map φ
      let mgy := (P.pullbackFunctor g).map φ
      let mfx := (P.pullbackFunctor f).map mgy
      let lhs := mfg ≫ (component y).hom
      let rhs := (component x).hom ≫ mfx
      change lhs.1 = rhs.1
      let : p.IsStronglyCartesian f (P.pullbackMap f (P.pullback g y)) :=
        P.pullbackMap_isStronglyCartesian f (P.pullback g y)
      let : p.IsStronglyCartesian g (P.pullbackMap g y) :=
        P.pullbackMap_isStronglyCartesian g y
      let : p.IsStronglyCartesian (f ≫ g)
          (P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y) := by
        exact @Functor.IsStronglyCartesian.comp _ _ _ _ p R S T _ _ _ f g _ _
          (P.pullbackMap_isStronglyCartesian f (P.pullback g y))
          (P.pullbackMap_isStronglyCartesian g y)
      have hfg : mfg.1 ≫ P.pullbackMap (f ≫ g) y =
          P.pullbackMap (f ≫ g) x ≫ φ.1 := by
        exact pullbackMap_fac (f ≫ g) φ
      have hf : mfx.1 ≫ P.pullbackMap f (P.pullback g y) =
          P.pullbackMap f (P.pullback g x) ≫ mgy.1 := by
        exact pullbackMap_fac f mgy
      have hg : mgy.1 ≫ P.pullbackMap g y =
          P.pullbackMap g x ≫ φ.1 := by
        exact pullbackMap_fac g φ
      have hL : p.IsHomLift (𝟙 R)
          (Functor.Fiber.fiberInclusion.map lhs) := by
        let : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map mfg) := mfg.2
        let : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map (component y).hom) :=
          by
            change p.IsHomLift (𝟙 R) (component y).hom.1
            exact (component y).hom.2
        infer_instance
      have hR : p.IsHomLift (𝟙 R)
          (Functor.Fiber.fiberInclusion.map rhs) := by
        let : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map (component x).hom) :=
          by
            change p.IsHomLift (𝟙 R) (component x).hom.1
            exact (component x).hom.2
        let : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map mfx) := by
          change p.IsHomLift (𝟙 R) mfx.1
          exact mfx.2
        infer_instance
      have hL' : p.IsHomLift (𝟙 R) lhs.1 := by
        change p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map lhs)
        exact hL
      have hR' : p.IsHomLift (𝟙 R) rhs.1 := by
        change p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map rhs)
        exact hR
      let : p.IsHomLift (𝟙 R) lhs.1 := hL'
      let : p.IsHomLift (𝟙 R) rhs.1 := hR'
      let : p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map lhs) := hL
      let : p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map rhs) := hR
      have hEq : lhs.1 ≫ P.pullbackMap f (P.pullback g y) ≫
            P.pullbackMap g y = rhs.1 ≫ P.pullbackMap f (P.pullback g y) ≫
            P.pullbackMap g y := by
        have hf' :
            (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).map mfx ≫
                P.pullbackMap f (P.pullback g y) =
              P.pullbackMap f (P.pullback g x) ≫
                (Functor.Fiber.fiberInclusion : Functor.Fiber p S ⥤ X).map mgy := by
          exact hf
        have hg' :
            (Functor.Fiber.fiberInclusion : Functor.Fiber p S ⥤ X).map mgy ≫
                P.pullbackMap g y =
              P.pullbackMap g x ≫
                (Functor.Fiber.fiberInclusion : Functor.Fiber p T ⥤ X).map φ := by
          exact hg
        have ha1 :
            (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).map mfx ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y =
              ((Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).map mfx ≫
                P.pullbackMap f (P.pullback g y)) ≫ P.pullbackMap g y := by
          exact (Category.assoc _ _ _).symm
        have ha2 :
            (P.pullbackMap f (P.pullback g x) ≫
              (Functor.Fiber.fiberInclusion : Functor.Fiber p S ⥤ X).map mgy) ≫
                P.pullbackMap g y =
              P.pullbackMap f (P.pullback g x) ≫
                ((Functor.Fiber.fiberInclusion : Functor.Fiber p S ⥤ X).map mgy ≫
                  P.pullbackMap g y) := by
          exact Category.assoc _ _ _
        have hright0 :
            (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).map mfx ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y =
              P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x ≫
                (Functor.Fiber.fiberInclusion : Functor.Fiber p T ⥤ X).map φ := by
          exact ha1.trans ((congrArg (fun k => k ≫ P.pullbackMap g y) hf').trans
            (ha2.trans (congrArg (fun k =>
              P.pullbackMap f (P.pullback g x) ≫ k) hg')))
        have hright1 :
            (component x).hom.1 ≫ P.pullbackMap f (P.pullback g x) ≫
                P.pullbackMap g x ≫ φ.1 =
              (component x).hom.1 ≫ mfx.1 ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y := by
          exact congrArg (fun k => (component x).hom.1 ≫ k) hright0.symm
        have hlhs :
            lhs.1 = mfg.1 ≫ (component y).hom.1 := by
          dsimp [lhs]
          rfl
        have hrhs :
            rhs.1 = (component x).hom.1 ≫ mfx.1 := by
          dsimp [rhs]
          rfl
        have hfirst :
            mfg.1 ≫ (component y).hom.1 ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y =
              mfg.1 ≫ P.pullbackMap (f ≫ g) y := by
          exact congrArg (fun k => mfg.1 ≫ k) (component_fac y)
        have hthird0 :
            P.pullbackMap (f ≫ g) x ≫ φ.1 =
              ((component x).hom.1 ≫
                P.pullbackMap f (P.pullback g x) ≫
                P.pullbackMap g x) ≫ φ.1 := by
          exact congrArg (fun k => k ≫ φ.1) (component_fac x).symm
        have hthirdassoc :
            ((component x).hom.1 ≫
                P.pullbackMap f (P.pullback g x) ≫
                P.pullbackMap g x) ≫ φ.1 =
              (component x).hom.1 ≫
                P.pullbackMap f (P.pullback g x) ≫
                P.pullbackMap g x ≫ φ.1 := by
          exact
            (Category.assoc (component x).hom.1
              (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x)
              φ.1).trans
              (congrArg (fun k => (component x).hom.1 ≫ k)
                (Category.assoc (P.pullbackMap f (P.pullback g x))
                  (P.pullbackMap g x) φ.1))
        have hthird := hthird0.trans hthirdassoc
        have hchain := hfirst.trans (hfg.trans (hthird.trans hright1))
        have hassocL :
            (mfg.1 ≫ (component y).hom.1) ≫
                (P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y) =
              mfg.1 ≫ (component y).hom.1 ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y := by
          exact Category.assoc _ _ _
        have hassocR :
            ((component x).hom.1 ≫ mfx.1) ≫
                (P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y) =
              (component x).hom.1 ≫ mfx.1 ≫
                P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y := by
          exact Category.assoc _ _ _
        simpa only [hlhs, hrhs] using
          hassocL.trans (hchain.trans hassocR.symm)
      exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
        (f ≫ g) (P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y)
        (by infer_instance) _ _ (𝟙 R) lhs.1 rhs.1 hL' hR' hEq
    )
  refine ⟨α, ?_, ?_⟩
  · intro x
    change (component x).hom.1 ≫ P.pullbackMap f (P.pullback g x) ≫
      P.pullbackMap g x = P.pullbackMap (f ≫ g) x
    exact component_fac x
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext x
    apply Functor.Fiber.hom_ext
    change (β.hom.app x).1 = (α.hom.app x).1
    let : p.IsStronglyCartesian (f ≫ g)
        (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x) := by
      exact @Functor.IsStronglyCartesian.comp _ _ _ _ p R S T _ _ _ f g _ _
        (P.pullbackMap_isStronglyCartesian f (P.pullback g x))
        (P.pullbackMap_isStronglyCartesian g x)
    have hβlift : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x)) :=
      by
        change p.IsHomLift (𝟙 R) (β.hom.app x).1
        exact (β.hom.app x).2
    have hαlift : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x)) :=
      by
        change p.IsHomLift (𝟙 R) (α.hom.app x).1
        exact (α.hom.app x).2
    have hβlift' : p.IsHomLift (𝟙 R) (β.hom.app x).1 := by
      change p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x))
      exact hβlift
    have hαlift' : p.IsHomLift (𝟙 R) (α.hom.app x).1 := by
      change p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x))
      exact hαlift
    let : p.IsHomLift (𝟙 R) (β.hom.app x).1 := hβlift'
    let : p.IsHomLift (𝟙 R) (α.hom.app x).1 := hαlift'
    let : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x)) := hβlift
    let : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x)) := hαlift
    have hEq : (β.hom.app x).1 ≫ P.pullbackMap f (P.pullback g x) ≫
          P.pullbackMap g x = (α.hom.app x).1 ≫
          P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x := by
      exact (hβ x).trans (component_fac x).symm
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (f ≫ g) (P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x)
      (by infer_instance) _ _ (𝟙 R) (β.hom.app x).1 (α.hom.app x).1
      hβlift' hαlift' hEq

theorem pullback_identity_iso
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) (U : C) :
    ∃! α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U),
      ∀ x : Functor.Fiber p U,
        Functor.Fiber.fiberInclusion.map (α.hom.app x) ≫
            P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
  let hom (x : Functor.Fiber p U) : x.1 ⟶ (P.pullback (𝟙 U) x).1 := by
    let : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    let : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    exact Functor.IsStronglyCartesian.map p (𝟙 U)
      (P.pullbackMap (𝟙 U) x)
      (f' := (𝟙 U : U ⟶ U)) (g := (𝟙 U : U ⟶ U)) (by simp)
      (𝟙 x.1)
  have hom_lift (x : Functor.Fiber p U) :
      p.IsHomLift (𝟙 U) (hom x) := by
    dsimp [hom]
    exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p
      _ _ _ _ (𝟙 U) (P.pullbackMap (𝟙 U) x) _ _ _
      (𝟙 U) (𝟙 U) (by simp) (𝟙 x.1) (IsHomLift.id x.2)
  have hom_fac (x : Functor.Fiber p U) :
      hom x ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
    dsimp [hom]
    let : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    let : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    exact Functor.IsStronglyCartesian.fac p (𝟙 U)
      (P.pullbackMap (𝟙 U) x)
      (f' := (𝟙 U : U ⟶ U)) (g := (𝟙 U : U ⟶ U)) (by simp)
      (𝟙 x.1)
  have pmap_lift (x : Functor.Fiber p U) :
      p.IsHomLift (𝟙 U) (P.pullbackMap (𝟙 U) x) := by
    let : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    infer_instance
  let component : ∀ x : Functor.Fiber p U,
      x ≅ P.pullback (𝟙 U) x := by
    intro x
    let homF : x ⟶ P.pullback (𝟙 U) x :=
      ⟨hom x, hom_lift x⟩
    let invF : P.pullback (𝟙 U) x ⟶ x :=
      ⟨P.pullbackMap (𝟙 U) x, pmap_lift x⟩
    refine { hom := homF, inv := invF, hom_inv_id := ?_, inv_hom_id := ?_ }
    · apply Functor.Fiber.hom_ext
      change hom x ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
      exact hom_fac x
    · apply Functor.Fiber.hom_ext
      change P.pullbackMap (𝟙 U) x ≫ hom x =
        𝟙 (P.pullback (𝟙 U) x).1
      let : p.IsStronglyCartesian (𝟙 U)
          (P.pullbackMap (𝟙 U) x) :=
        P.pullbackMap_isStronglyCartesian (𝟙 U) x
      let : p.IsHomLift (𝟙 U)
          (P.pullbackMap (𝟙 U) x) := pmap_lift x
      let : p.IsHomLift (𝟙 U) (hom x) := hom_lift x
      let hcomp : p.IsHomLift (𝟙 U)
          (P.pullbackMap (𝟙 U) x ≫ hom x) :=
        IsHomLift.comp_of_lift_id p U (P.pullbackMap (𝟙 U) x) (hom x)
      let hid : p.IsHomLift (𝟙 U)
          (𝟙 (P.pullback (𝟙 U) x).1) :=
        IsHomLift.id (P.pullback (𝟙 U) x).2
      have hEq :
          (P.pullbackMap (𝟙 U) x ≫ hom x) ≫
              P.pullbackMap (𝟙 U) x =
            (𝟙 (P.pullback (𝟙 U) x).1) ≫
              P.pullbackMap (𝟙 U) x := by
        have h₁ := Category.assoc (P.pullbackMap (𝟙 U) x)
          (hom x) (P.pullbackMap (𝟙 U) x)
        have h₂ := congrArg (fun k => P.pullbackMap (𝟙 U) x ≫ k)
          (hom_fac x)
        have h₃ := Category.comp_id (P.pullbackMap (𝟙 U) x)
        have h₄ := Category.id_comp (P.pullbackMap (𝟙 U) x)
        exact h₁.trans (h₂.trans (h₃.trans h₄.symm))
      exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
        (𝟙 U) (P.pullbackMap (𝟙 U) x)
        (P.pullbackMap_isStronglyCartesian (𝟙 U) x)
        _ _ (𝟙 U) (P.pullbackMap (𝟙 U) x ≫ hom x)
        (𝟙 (P.pullback (𝟙 U) x).1) hcomp hid hEq
  have pullbackMap_fac {A B : C} (h : A ⟶ B)
      {x y : Functor.Fiber p B} (φ : x ⟶ y) :
      ((P.pullbackFunctor h).map φ).1 ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1 := by
    let : p.IsHomLift (𝟙 B) φ.1 := φ.2
    let : p.IsStronglyCartesian h (P.pullbackMap h y) :=
      P.pullbackMap_isStronglyCartesian h y
    let : p.IsStronglyCartesian h (P.pullbackMap h x) :=
      P.pullbackMap_isStronglyCartesian h x
    have hφ' : p.IsHomLift h (P.pullbackMap h x ≫ φ.1) := by
      exact IsHomLift.comp_lift_id_right' p h (P.pullbackMap h x) B φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ p
        _ _ _ _ h (P.pullbackMap h y) _ _ _ (𝟙 A) h (by simp)
        (P.pullbackMap h x ≫ φ.1) hφ') ≫ P.pullbackMap h y =
        P.pullbackMap h x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac p h (P.pullbackMap h y)
      (f' := h) (g := 𝟙 A) (by simp) (P.pullbackMap h x ≫ φ.1)
  have component_fac (x : Functor.Fiber p U) :
      (component x).hom.1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
    change hom x ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
    exact hom_fac x
  let α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U) :=
    NatIso.ofComponents component (by
      intro x y φ
      apply Functor.Fiber.hom_ext
      let lhs := φ ≫ (component y).hom
      let rhs := (component x).hom ≫ (P.pullbackFunctor (𝟙 U)).map φ
      change lhs.1 = rhs.1
      let : p.IsStronglyCartesian (𝟙 U)
          (P.pullbackMap (𝟙 U) y) :=
        P.pullbackMap_isStronglyCartesian (𝟙 U) y
      have hleft : lhs.1 ≫ P.pullbackMap (𝟙 U) y = φ.1 := by
        dsimp [lhs]
        calc
          (φ.1 ≫ (component y).hom.1) ≫ P.pullbackMap (𝟙 U) y =
              φ.1 ≫ ((component y).hom.1 ≫
                P.pullbackMap (𝟙 U) y) := Category.assoc _ _ _
          _ = φ.1 ≫ 𝟙 y.1 := by rw [component_fac y]
          _ = φ.1 := by simp
      have hright : rhs.1 ≫ P.pullbackMap (𝟙 U) y = φ.1 := by
        dsimp [rhs]
        calc
          ((component x).hom ≫
              (P.pullbackFunctor (𝟙 U)).map φ).1 ≫
              P.pullbackMap (𝟙 U) y =
              (component x).hom.1 ≫
                (((P.pullbackFunctor (𝟙 U)).map φ).1 ≫
                  P.pullbackMap (𝟙 U) y) := by
            exact Category.assoc (component x).hom.1
              ((P.pullbackFunctor (𝟙 U)).map φ).1
              (P.pullbackMap (𝟙 U) y)
          _ = (component x).hom.1 ≫
              (P.pullbackMap (𝟙 U) x ≫ φ.1) := by
            exact congrArg (fun k => (component x).hom.1 ≫ k)
              (pullbackMap_fac (𝟙 U) φ)
          _ = ((component x).hom.1 ≫ P.pullbackMap (𝟙 U) x) ≫
              φ.1 := (Category.assoc _ _ _).symm
          _ = 𝟙 x.1 ≫ φ.1 := by rw [component_fac x]
          _ = φ.1 := by simp
      have hL : p.IsHomLift (𝟙 U) lhs.1 := lhs.2
      have hR : p.IsHomLift (𝟙 U) rhs.1 := rhs.2
      exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
        (𝟙 U) (P.pullbackMap (𝟙 U) y)
        (P.pullbackMap_isStronglyCartesian (𝟙 U) y)
        _ _ (𝟙 U) lhs.1 rhs.1 hL hR (hleft.trans hright.symm))
  refine ⟨α, ?_, ?_⟩
  · intro x
    exact component_fac x
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext x
    apply Functor.Fiber.hom_ext
    change (β.hom.app x).1 = (α.hom.app x).1
    let : p.IsStronglyCartesian (𝟙 U)
        (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    have hβlift : p.IsHomLift (𝟙 U) (β.hom.app x).1 := by
      change p.IsHomLift (𝟙 U)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x))
      exact (β.hom.app x).2
    have hαlift : p.IsHomLift (𝟙 U) (α.hom.app x).1 := by
      change p.IsHomLift (𝟙 U)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x))
      exact (α.hom.app x).2
    have hEq : (β.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x =
        (α.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x := by
      exact (hβ x).trans (component_fac x).symm
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 U) (P.pullbackMap (𝟙 U) x)
      (P.pullbackMap_isStronglyCartesian (𝟙 U) x)
      _ _ (𝟙 U) (β.hom.app x).1 (α.hom.app x).1 hβlift hαlift hEq

/- A pseudofunctor-compatible packaging of the choice.  The object and map
   fields explicitly identify the Mathlib pseudofunctor with the fibre
   categories and the `pullbackFunctor`s above; its unit, composition, and
   coherence laws are those of Mathlib's `Pseudofunctor`. -/
structure PullbackPseudofunctorData
    {X : Type u₁} [Category.{v₁} X] {C : Type u₂} [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  value : PseudofunctorFromCategory Cᵒᵖ
    (AssociatedTwoOneCategory (Cat.{v₁, u₁}))
  object_fibre : ∀ (U : C),
    pseudofunctorObject value (Opposite.op U) =
      Bicategory.Pith.mk (Cat.of (Functor.Fiber p U))
  map_pullback : ∀ {R S : C} (f : R ⟶ S),
    Nonempty
      (eqToHom (congrArg Bicategory.Pith.as (object_fibre S).symm) ≫
          (pseudofunctorMap value f.op).of ≫
          eqToHom (congrArg Bicategory.Pith.as (object_fibre R)) ≅
        (P.pullbackFunctor f).toCatHom)

theorem pullback_pseudofunctor_exists
    {X : Type u₁} [Category.{v₁} X] {C : Type u₂} [Category.{v₂} C]
    (p : X ⥤ C) [p.IsFibered] (P : PullbackChoice p) :
    Nonempty (PullbackPseudofunctorData p P) := by
  sorry

/-! ## Fibred categories over a fixed category -/

def MapsStronglyCartesian
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ C) (q : B ⥤ C) (F : A ⥤ B) : Prop :=
  ∀ {a b : A} (φ : a ⟶ b),
    Functor.IsStronglyCartesian p (p.map φ) φ →
      Functor.IsStronglyCartesian q (q.map (F.map φ)) (F.map φ)

/- The source's objects are fibred categories over `C`. -/
structure FibredCategoryOver (C : Cat.{v, u}) where
  underlying : CategoryOver C
  isFibred : (structureFunctor underlying).IsFibered

attribute [instance] FibredCategoryOver.isFibred

/- A source 1-morphism is a functor over `C` which preserves strongly
   cartesian arrows.  The base morphism in the target is written using the
   target structure functor; the strict triangle in `CategoryOver` identifies
   it with the source base morphism. -/
structure FibredCategoryOverHom {C : Cat.{v, u}}
    (X Y : FibredCategoryOver C) where
  underlying : CategoryOverHom X.underlying Y.underlying
  preserves : MapsStronglyCartesian
    (structureFunctor X.underlying) (structureFunctor Y.underlying)
    (overFunctor underlying)

namespace FibredCategoryOverHom

@[ext]
lemma ext {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (h : F.underlying = G.underlying) : F = G := by
  cases F
  cases G
  cases h
  rfl

def id {C : Cat.{v, u}} (X : FibredCategoryOver C) :
    FibredCategoryOverHom X X where
  underlying := CategoryOver.id X.underlying
  preserves := by
    intro a b φ hφ
    change (structureFunctor X.underlying).IsStronglyCartesian
      ((structureFunctor X.underlying).map φ) φ
    exact hφ

def comp {C : Cat.{v, u}} {X Y Z : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) (G : FibredCategoryOverHom Y Z) :
    FibredCategoryOverHom X Z where
  underlying := CategoryOver.comp F.underlying G.underlying
  preserves := by
    intro a b φ hφ
    change (structureFunctor Z.underlying).IsStronglyCartesian
      ((structureFunctor Z.underlying).map
        ((overFunctor G.underlying).map ((overFunctor F.underlying).map φ)))
      ((overFunctor G.underlying).map ((overFunctor F.underlying).map φ))
    exact G.preserves ((overFunctor F.underlying).map φ) (F.preserves φ hφ)

end FibredCategoryOverHom

def fibredOverNatTransId {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    OverNatTrans F.underlying F.underlying :=
  { toNatTrans := 𝟙 (overFunctor F.underlying)
    over := by
      intro Z
      simp [overIdentityComponent] }

def fibredOverNatTransComp {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C}
    {F G H : FibredCategoryOverHom X Y}
    (η : OverNatTrans F.underlying G.underlying)
    (θ : OverNatTrans G.underlying H.underlying) :
    OverNatTrans F.underlying H.underlying :=
  { toNatTrans := η.toNatTrans ≫ θ.toNatTrans
    over := by
      intro Z
      simp only [NatTrans.comp_app, Functor.map_comp]
      rw [η.over Z, θ.over Z]
      simp [overIdentityComponent] }

instance fibredCategoryOverHomCategory {C : Cat.{v, u}}
    (X Y : FibredCategoryOver C) : Category (FibredCategoryOverHom X Y) where
  Hom F G := OverNatTrans F.underlying G.underlying
  id F := fibredOverNatTransId F
  comp η θ := fibredOverNatTransComp η θ
  id_comp := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransId, fibredOverNatTransComp]
  comp_id := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransId, fibredOverNatTransComp]
  assoc := by
    intros
    apply OverNatTrans.ext
    simp [fibredOverNatTransComp, Category.assoc]

/- The fixed-base 2-category is made usable as a bicategory.  The preservation
   proofs are proposition-valued and are left to the proof stage; the carrier,
   composition, whiskering, and coherence maps are the canonical ones from
   `CategoryOver`. -/
def fibredHomIsoOfUnderlying {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} {F G : FibredCategoryOverHom X Y}
  (e : F.underlying ≅ G.underlying) : F ≅ G where
  hom :=
    { toNatTrans := e.hom.toNatTrans
      over := e.hom.over }
  inv :=
    { toNatTrans := e.inv.toNatTrans
      over := e.inv.over }
  hom_inv_id := by
    apply OverNatTrans.ext
    change e.hom.toNatTrans ≫ e.inv.toNatTrans = 𝟙 (overFunctor F.underlying)
    exact congrArg (fun η : OverNatTrans F.underlying F.underlying => η.toNatTrans)
      e.hom_inv_id
  inv_hom_id := by
    apply OverNatTrans.ext
    change e.inv.toNatTrans ≫ e.hom.toNatTrans = 𝟙 (overFunctor G.underlying)
    exact congrArg (fun η : OverNatTrans G.underlying G.underlying => η.toNatTrans)
      e.inv_hom_id

def fibredWhiskerLeft {C : Cat.{v, u}}
    {X Y Z : FibredCategoryOver C} (F : FibredCategoryOverHom X Y)
    {G H : FibredCategoryOverHom Y Z}
    (η : OverNatTrans G.underlying H.underlying) :
    OverNatTrans (FibredCategoryOverHom.comp F G).underlying
      (FibredCategoryOverHom.comp F H).underlying :=
  overWhiskerLeft F.underlying η

def fibredWhiskerRight {C : Cat.{v, u}}
    {X Y Z : FibredCategoryOver C}
    {F G : FibredCategoryOverHom X Y} (η : OverNatTrans F.underlying G.underlying)
    (H : FibredCategoryOverHom Y Z) :
    OverNatTrans (FibredCategoryOverHom.comp F H).underlying
      (FibredCategoryOverHom.comp G H).underlying :=
  overWhiskerRight η H.underlying

noncomputable instance fibredCategoriesOverBicategory {C : Cat.{v, u}} :
    Bicategory (FibredCategoryOver C) where
  Hom := FibredCategoryOverHom
  id := FibredCategoryOverHom.id
  comp := FibredCategoryOverHom.comp
  homCategory := fibredCategoryOverHomCategory
  whiskerLeft := fibredWhiskerLeft
  whiskerRight := fibredWhiskerRight
  associator F G H :=
    fibredHomIsoOfUnderlying
      (Bicategory.associator (B := CategoryOver C)
        F.underlying G.underlying H.underlying)
  leftUnitor F :=
    fibredHomIsoOfUnderlying
      (Bicategory.leftUnitor (B := CategoryOver C) F.underlying)
  rightUnitor F :=
    fibredHomIsoOfUnderlying
      (Bicategory.rightUnitor (B := CategoryOver C) F.underlying)
  whiskerLeft_id := by
    intro X Y Z F G
    apply OverNatTrans.ext
    change (overWhiskerLeft F.underlying (𝟙 G.underlying)).toNatTrans =
      ((𝟙 (CategoryOver.comp F.underlying G.underlying)) :
        OverNatTrans (CategoryOver.comp F.underlying G.underlying)
          (CategoryOver.comp F.underlying G.underlying)).toNatTrans
    exact congrArg
      (fun η : OverNatTrans (CategoryOver.comp F.underlying G.underlying)
          (CategoryOver.comp F.underlying G.underlying) => η.toNatTrans)
      (Bicategory.whiskerLeft_id (B := CategoryOver C)
        F.underlying G.underlying)
  whiskerLeft_comp := by
    intro X Y Z f g h i η θ
    apply OverNatTrans.ext
    change (overWhiskerLeft f.underlying (η ≫ θ)).toNatTrans =
      (overWhiskerLeft f.underlying η).toNatTrans ≫
        (overWhiskerLeft f.underlying θ).toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.whiskerLeft_comp (B := CategoryOver C)
        f.underlying η θ)
  id_whiskerLeft := by
    intro X Y F G η
    apply OverNatTrans.ext
    change (overWhiskerLeft (CategoryOver.id X.underlying) η).toNatTrans =
      (Bicategory.leftUnitor (B := CategoryOver C) F.underlying).hom.toNatTrans ≫
        η.toNatTrans ≫
          (Bicategory.leftUnitor (B := CategoryOver C) G.underlying).inv.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.id_whiskerLeft (B := CategoryOver C) η)
  comp_whiskerLeft := by
    intro W X Y Z F G H I η
    apply OverNatTrans.ext
    change (overWhiskerLeft (CategoryOver.comp F.underlying G.underlying) η).toNatTrans =
      (Bicategory.associator (B := CategoryOver C)
          F.underlying G.underlying H.underlying).hom.toNatTrans ≫
        (overWhiskerLeft F.underlying (overWhiskerLeft G.underlying η)).toNatTrans ≫
          (Bicategory.associator (B := CategoryOver C)
            F.underlying G.underlying I.underlying).inv.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.comp_whiskerLeft (B := CategoryOver C)
        F.underlying G.underlying η)
  id_whiskerRight := by
    intro X Y Z F G
    apply OverNatTrans.ext
    change (overWhiskerRight (𝟙 F.underlying) G.underlying).toNatTrans =
      ((𝟙 (CategoryOver.comp F.underlying G.underlying)) :
        OverNatTrans (CategoryOver.comp F.underlying G.underlying)
          (CategoryOver.comp F.underlying G.underlying)).toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.id_whiskerRight (B := CategoryOver C)
        F.underlying G.underlying)
  comp_whiskerRight := by
    intro X Y Z F G H η θ I
    apply OverNatTrans.ext
    change (overWhiskerRight (η ≫ θ) I.underlying).toNatTrans =
      (overWhiskerRight η I.underlying).toNatTrans ≫
        (overWhiskerRight θ I.underlying).toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.comp_whiskerRight (B := CategoryOver C)
        η θ I.underlying)
  whiskerRight_id := by
    intro X Y F G η
    apply OverNatTrans.ext
    change (overWhiskerRight η (CategoryOver.id Y.underlying)).toNatTrans =
      (Bicategory.rightUnitor (B := CategoryOver C) F.underlying).hom.toNatTrans ≫
        η.toNatTrans ≫
          (Bicategory.rightUnitor (B := CategoryOver C) G.underlying).inv.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.whiskerRight_id (B := CategoryOver C) η)
  whiskerRight_comp := by
    intro W X Y Z F G η H I
    apply OverNatTrans.ext
    change (overWhiskerRight η (CategoryOver.comp H.underlying I.underlying)).toNatTrans =
      (Bicategory.associator (B := CategoryOver C)
          F.underlying H.underlying I.underlying).inv.toNatTrans ≫
        (overWhiskerRight (overWhiskerRight η H.underlying)
          I.underlying).toNatTrans ≫
          (Bicategory.associator (B := CategoryOver C)
            G.underlying H.underlying I.underlying).hom.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.whiskerRight_comp (B := CategoryOver C)
        η H.underlying I.underlying)
  whisker_assoc := by
    intro W X Y Z F G H η I
    apply OverNatTrans.ext
    change (overWhiskerRight (overWhiskerLeft F.underlying η)
        I.underlying).toNatTrans =
      (Bicategory.associator (B := CategoryOver C)
          F.underlying G.underlying I.underlying).hom.toNatTrans ≫
        (overWhiskerLeft F.underlying
          (overWhiskerRight η I.underlying)).toNatTrans ≫
          (Bicategory.associator (B := CategoryOver C)
            F.underlying H.underlying I.underlying).inv.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.whisker_assoc (B := CategoryOver C)
        F.underlying η I.underlying)
  whisker_exchange := by
    intro X Y Z F G H I η θ
    apply OverNatTrans.ext
    change (overWhiskerLeft F.underlying θ).toNatTrans ≫
        (overWhiskerRight η I.underlying).toNatTrans =
      (overWhiskerRight η H.underlying).toNatTrans ≫
        (overWhiskerLeft G.underlying θ).toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.whisker_exchange (B := CategoryOver C) η θ)
  pentagon := by
    intro V W X Y Z F G H I
    apply OverNatTrans.ext
    change
      (overWhiskerRight
          (Bicategory.associator (B := CategoryOver C)
            F.underlying G.underlying H.underlying).hom I.underlying).toNatTrans ≫
        (Bicategory.associator (B := CategoryOver C)
          F.underlying (CategoryOver.comp G.underlying H.underlying)
            I.underlying).hom.toNatTrans ≫
          (overWhiskerLeft F.underlying
            (Bicategory.associator (B := CategoryOver C)
              G.underlying H.underlying I.underlying).hom).toNatTrans =
        (Bicategory.associator (B := CategoryOver C)
          (CategoryOver.comp F.underlying G.underlying)
            H.underlying I.underlying).hom.toNatTrans ≫
          (Bicategory.associator (B := CategoryOver C)
            F.underlying G.underlying (CategoryOver.comp H.underlying I.underlying)).hom.toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.pentagon (B := CategoryOver C)
        F.underlying G.underlying H.underlying I.underlying)
  triangle := by
    intro X Y Z F G
    apply OverNatTrans.ext
    change
      (Bicategory.associator (B := CategoryOver C)
          F.underlying (CategoryOver.id Y.underlying) G.underlying).hom.toNatTrans ≫
        (overWhiskerLeft F.underlying
          (Bicategory.leftUnitor (B := CategoryOver C) G.underlying).hom).toNatTrans =
      (overWhiskerRight
        (Bicategory.rightUnitor (B := CategoryOver C) F.underlying).hom
          G.underlying).toNatTrans
    exact congrArg (fun q => q.toNatTrans)
      (Bicategory.triangle (B := CategoryOver C)
        F.underlying G.underlying)

noncomputable instance fibredCategoriesOverStrict {C : Cat.{v, u}} :
    Bicategory.Strict (FibredCategoryOver C) := by
  refine {
    id_comp := ?_
    comp_id := ?_
    assoc := ?_
    leftUnitor_eqToIso := ?_
    rightUnitor_eqToIso := ?_
    associator_eqToIso := ?_ }
  · intro X Y F
    apply FibredCategoryOverHom.ext
    exact Bicategory.Strict.id_comp (B := CategoryOver C) F.underlying
  · intro X Y F
    apply FibredCategoryOverHom.ext
    exact Bicategory.Strict.comp_id (B := CategoryOver C) F.underlying
  · intro W X Y Z F G H
    apply FibredCategoryOverHom.ext
    exact Bicategory.Strict.assoc (B := CategoryOver C)
      F.underlying G.underlying H.underlying
  · intros
    rfl
  · intros
    rfl
  · intros
    rfl

theorem fibredCategoriesOver_associated_two_one_category
    (C : Cat.{v, u}) :
    IsTwoOneCategory
      (AssociatedTwoOneCategory (FibredCategoryOver C)) := by
  infer_instance

/- Equivalence over `C`: the functors and the comparison isomorphisms are all
   morphisms in the already constructed category of categories over `C`. -/
def IsEquivalentOver {C : Cat.{v, u}}
    (X Y : CategoryOver C) : Prop :=
  ∃ (F : CategoryOverHom X Y) (G : CategoryOverHom Y X),
    Nonempty (CategoryOver.comp F G ≅ CategoryOver.id X) ∧
      Nonempty (CategoryOver.comp G F ≅ CategoryOver.id Y)

theorem equivalence_over_preserves_stronglyCartesian
    {C : Cat.{v, u}} {X Y : CategoryOver C}
    (F : CategoryOverHom X Y)
    (hF : ∃ G : CategoryOverHom Y X,
      Nonempty (CategoryOver.comp F G ≅ CategoryOver.id X) ∧
        Nonempty (CategoryOver.comp G F ≅ CategoryOver.id Y))
    {a b : X.left} (φ : a ⟶ b)
    (hφ : Functor.IsStronglyCartesian (structureFunctor X) 
      ((structureFunctor X).map φ) φ) :
    Functor.IsStronglyCartesian (structureFunctor Y)
      ((structureFunctor Y).map ((overFunctor F).map φ)) ((overFunctor F).map φ) := by
  obtain ⟨G, ⟨eFG⟩, ⟨eGF⟩⟩ := hF
  let eFG' : overFunctor F ⋙ overFunctor G ≅ 𝟭 X.left := by
    refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eFG.hom.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eFG.inv.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eFG.hom.toNatTrans ≫ eFG.inv.toNatTrans =
            𝟙 (overFunctor F ⋙ overFunctor G) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.comp F G) (CategoryOver.comp F G) =>
              η.toNatTrans) eFG.hom_inv_id)
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eFG.inv.toNatTrans ≫ eFG.hom.toNatTrans =
            𝟙 (𝟭 X.left) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.id X) (CategoryOver.id X) =>
              η.toNatTrans) eFG.inv_hom_id)
  let eGF' : overFunctor G ⋙ overFunctor F ≅ 𝟭 Y.left := by
    refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eGF.hom.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eGF.inv.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eGF.hom.toNatTrans ≫ eGF.inv.toNatTrans =
            𝟙 (overFunctor G ⋙ overFunctor F) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.comp G F) (CategoryOver.comp G F) =>
              η.toNatTrans) eGF.hom_inv_id)
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eGF.inv.toNatTrans ≫ eGF.hom.toNatTrans =
            𝟙 (𝟭 Y.left) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.id Y) (CategoryOver.id Y) =>
              η.toNatTrans) eGF.inv_hom_id)
  let : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map φ) φ := hφ
  let αa := eFG'.hom.app a
  let αb := eFG'.hom.app b
  let : IsIso αa := by
    change IsIso (eFG'.hom.app a)
    exact NatIso.hom_app_isIso eFG' a
  let : IsIso αb := by
    change IsIso (eFG'.hom.app b)
    exact NatIso.hom_app_isIso eFG' b
  let : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map αa) αa := by infer_instance
  let : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map αb) αb := by infer_instance
  let αbinv := inv αb
  let : IsIso αbinv := by
    dsimp [αbinv]
    infer_instance
  let : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map αbinv) αbinv := by infer_instance
  have hnat : (overFunctor F ⋙ overFunctor G).map φ ≫ αb = αa ≫ φ := by
    exact eFG'.hom.naturality φ
  have hGFφ : (overFunctor F ⋙ overFunctor G).map φ = αa ≫ φ ≫ αbinv := by
    apply (cancel_mono αb).1
    calc
      (overFunctor F ⋙ overFunctor G).map φ ≫ αb = αa ≫ φ := hnat
      _ = (αa ≫ φ ≫ αbinv) ≫ αb := by simp [αbinv, Category.assoc]
  have hcomp : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map (αa ≫ φ ≫ αbinv)) (αa ≫ φ ≫ αbinv) := by
    simpa only [Functor.map_comp] using
      (inferInstance : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map αa ≫
          (structureFunctor X).map φ ≫
            (structureFunctor X).map αbinv) (αa ≫ φ ≫ αbinv))
  have hGFstrong : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map ((overFunctor F ⋙ overFunctor G).map φ))
      ((overFunctor F ⋙ overFunctor G).map φ) := by
    rw [hGFφ]
    exact hcomp
  constructor
  intro c g τ hτ
  let hGc := congrArg (fun K : Y.left ⥤ C => K.obj c) (overFunctor_comm G)
  let hGFa := congrArg (fun K : Y.left ⥤ C =>
    K.obj ((overFunctor F).obj a)) (overFunctor_comm G)
  let hGFb := congrArg (fun K : Y.left ⥤ C =>
    K.obj ((overFunctor F).obj b)) (overFunctor_comm G)
  let hFGc := congrArg (fun K : X.left ⥤ C =>
    K.obj ((overFunctor G).obj c)) (overFunctor_comm F)
  let hFGa := congrArg (fun K : X.left ⥤ C =>
    K.obj ((overFunctor G).obj ((overFunctor F).obj a))) (overFunctor_comm F)
  let gX := eqToHom hGc ≫ g ≫ eqToHom hGFa.symm
  have hGmapτ : (structureFunctor X).map ((overFunctor G).map τ) =
      eqToHom hGc ≫ (structureFunctor Y).map τ ≫ eqToHom hGFb.symm := by
    exact Functor.congr_hom (overFunctor_comm G) τ
  have hGFmapφ : (structureFunctor X).map
      ((overFunctor G).map ((overFunctor F).map φ)) =
      eqToHom hGFa ≫ (structureFunctor Y).map ((overFunctor F).map φ) ≫
        eqToHom hGFb.symm := by
    exact Functor.congr_hom (overFunctor_comm G) ((overFunctor F).map φ)
  let : (structureFunctor Y).IsHomLift
      (g ≫ (structureFunctor Y).map ((overFunctor F).map φ)) τ := hτ
  have hτmap : g ≫ (structureFunctor Y).map ((overFunctor F).map φ) =
      (structureFunctor Y).map τ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (structureFunctor Y)
      (g ≫ (structureFunctor Y).map ((overFunctor F).map φ)) τ
  have hGτfactor : (structureFunctor X).map ((overFunctor G).map τ) =
      gX ≫ (structureFunctor X).map
        ((overFunctor G).map ((overFunctor F).map φ)) := by
    rw [hGmapτ, hGFmapφ, ← hτmap]
    simp [gX, Category.assoc]
  have hGτ : (structureFunctor X).IsHomLift
      (gX ≫ (structureFunctor X).map
        ((overFunctor G).map ((overFunctor F).map φ)))
      ((overFunctor G).map τ) := by
    have hmap : (structureFunctor X).IsHomLift
        ((structureFunctor X).map ((overFunctor G).map τ))
        ((overFunctor G).map τ) := inferInstance
    rw [hGτfactor] at hmap
    exact hmap
  let : (structureFunctor X).IsHomLift
      (gX ≫ (structureFunctor X).map
        ((overFunctor G).map ((overFunctor F).map φ)))
      ((overFunctor G).map τ) := hGτ
  let : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map
        ((overFunctor G).map ((overFunctor F).map φ)))
      ((overFunctor G).map ((overFunctor F).map φ)) := by
    simpa only [Functor.comp_map] using hGFstrong
  obtain ⟨δ, ⟨hδ, hδeq⟩, hδuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property (structureFunctor X)
      ((structureFunctor X).map ((overFunctor G).map ((overFunctor F).map φ)))
      ((overFunctor G).map ((overFunctor F).map φ)) gX
      ((structureFunctor X).map ((overFunctor G).map τ)) hGτfactor
      ((overFunctor G).map τ)
  let εc := eGF'.inv.app c
  let εa := eGF'.hom.app ((overFunctor F).obj a)
  let εb := eGF'.hom.app ((overFunctor F).obj b)
  have hFmapδ : (structureFunctor Y).map ((overFunctor F).map δ) =
      eqToHom hFGc ≫ (structureFunctor X).map δ ≫ eqToHom hFGa.symm := by
    exact Functor.congr_hom (overFunctor_comm F) δ
  have hεc : (structureFunctor Y).map εc =
      eqToHom (hGc.symm.trans hFGc.symm) := by
    simpa [εc, eGF', overFunctor, CategoryOver.comp, CategoryOver.id,
      CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor, Cat.Hom.id_obj, overIdentityComponent] using
      eGF.inv.over c
  have hεa : (structureFunctor Y).map εa =
      eqToHom (hFGa.trans hGFa) := by
    simpa [εa, eGF', overFunctor, CategoryOver.comp, CategoryOver.id,
      CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
      Cat.Hom.id_toFunctor, Cat.Hom.id_obj, overIdentityComponent] using
      eGF.hom.over ((overFunctor F).obj a)
  let : (structureFunctor X).IsHomLift gX δ := hδ
  have hδmap : gX = (structureFunctor X).map δ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (structureFunctor X) gX δ
  let χ := εc ≫ (overFunctor F).map δ ≫ εa
  have hχmap : (structureFunctor Y).map χ = g := by
    dsimp [χ]
    rw [Functor.map_comp, Functor.map_comp, hεc, hFmapδ, hεa, ← hδmap]
    simp [gX, Category.assoc]
  have hχlift : (structureFunctor Y).IsHomLift g χ := by
    have hmap : (structureFunctor Y).IsHomLift ((structureFunctor Y).map χ) χ :=
      inferInstance
    rw [hχmap] at hmap
    exact hmap
  have hχfac : χ ≫ (overFunctor F).map φ = τ := by
    dsimp [χ]
    calc
      (εc ≫ (overFunctor F).map δ ≫ εa) ≫ (overFunctor F).map φ =
          εc ≫ (overFunctor F).map δ ≫
            ((overFunctor G ⋙ overFunctor F).map ((overFunctor F).map φ) ≫ εb) := by
        dsimp [εa, εb]
        change
          (εc ≫ (overFunctor F).map δ ≫
              eGF'.hom.app ((overFunctor F).obj a)) ≫ (overFunctor F).map φ =
            εc ≫ (overFunctor F).map δ ≫
              ((overFunctor G ⋙ overFunctor F).map ((overFunctor F).map φ) ≫
                eGF'.hom.app ((overFunctor F).obj b))
        rw [eGF'.hom.naturality]
        simp [Category.assoc]
      _ = εc ≫ (overFunctor F).map
            (δ ≫ (overFunctor G).map ((overFunctor F).map φ)) ≫ εb := by
        simp only [Functor.comp_map]
        rw [← Category.assoc ((overFunctor F).map δ)
          ((overFunctor F).map ((overFunctor G).map ((overFunctor F).map φ))) εb]
        rw [← (overFunctor F).map_comp]
      _ = εc ≫ (overFunctor F).map ((overFunctor G).map τ) ≫ εb := by
        rw [hδeq]
      _ = τ := by
        have hn := eGF'.hom.naturality τ
        simp only [Functor.comp_map] at hn
        rw [hn]
        simp [εc]
  refine ⟨χ, ⟨hχlift, hχfac⟩, ?_⟩
  intro χ' hχ'
  rcases hχ' with ⟨hχ'lift, hχ'fac⟩
  let : (structureFunctor Y).IsHomLift g χ' := hχ'lift
  have hχ'map : g = (structureFunctor Y).map χ' :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (structureFunctor Y) g χ'
  let δ' := (overFunctor G).map χ'
  have hGmapχ' : (structureFunctor X).map δ' =
      eqToHom hGc ≫ (structureFunctor Y).map χ' ≫ eqToHom hGFa.symm := by
    exact Functor.congr_hom (overFunctor_comm G) χ'
  have hδ'map : gX = (structureFunctor X).map δ' := by
    dsimp [gX]
    rw [hχ'map]
    exact hGmapχ'.symm
  have hδ'lift : (structureFunctor X).IsHomLift gX δ' := by
    have hmap : (structureFunctor X).IsHomLift ((structureFunctor X).map δ') δ' :=
      inferInstance
    rw [← hδ'map] at hmap
    exact hmap
  have hδ'eq : δ' ≫ (overFunctor G).map ((overFunctor F).map φ) =
      (overFunctor G).map τ := by
    simpa only [δ', Functor.map_comp] using
      congrArg (overFunctor G).map hχ'fac
  have hδeq' : δ' = δ := hδuniq δ' ⟨hδ'lift, hδ'eq⟩
  have hχ'form : χ' = εc ≫ (overFunctor F).map δ' ≫ εa := by
    have hn := eGF'.hom.naturality χ'
    simp only [Functor.comp_map] at hn
    simp only [Functor.id_map] at hn
    calc
      χ' = 𝟙 _ ≫ χ' := by simp
      _ = (eGF'.inv.app _ ≫ eGF'.hom.app _) ≫ χ' := by simp
      _ = eGF'.inv.app _ ≫ (eGF'.hom.app _ ≫ χ') := by
        simp
      _ = eGF'.inv.app _ ≫
          ((overFunctor G ⋙ overFunctor F).map χ' ≫
            eGF'.hom.app ((overFunctor F).obj a)) := by
        rw [← hn]
        simp only [Functor.comp_map]
      _ = εc ≫ (overFunctor F).map δ' ≫ εa := by
        dsimp [εc, εa, δ']
  calc
    χ' = εc ≫ (overFunctor F).map δ' ≫ εa := hχ'form
    _ = εc ≫ (overFunctor F).map δ ≫ εa := by rw [hδeq']
    _ = χ := by rfl

theorem fibred_iff_equivalent_over
    {C : Cat.{v, u}} {X Y : CategoryOver C}
    (h : IsEquivalentOver X Y) :
    (structureFunctor X).IsFibered ↔ (structureFunctor Y).IsFibered := by
  obtain ⟨F, G, ⟨eFG⟩, ⟨eGF⟩⟩ := h
  let eFG' : overFunctor F ⋙ overFunctor G ≅ 𝟭 X.left := by
    refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eFG.hom.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eFG.inv.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eFG.hom.toNatTrans ≫ eFG.inv.toNatTrans =
            𝟙 (overFunctor F ⋙ overFunctor G) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.comp F G) (CategoryOver.comp F G) =>
              η.toNatTrans) eFG.hom_inv_id)
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eFG.inv.toNatTrans ≫ eFG.hom.toNatTrans =
            𝟙 (𝟭 X.left) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.id X) (CategoryOver.id X) =>
              η.toNatTrans) eFG.inv_hom_id)
  let eGF' : overFunctor G ⋙ overFunctor F ≅ 𝟭 Y.left := by
    refine { hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eGF.hom.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using eGF.inv.toNatTrans
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eGF.hom.toNatTrans ≫ eGF.inv.toNatTrans =
            𝟙 (overFunctor G ⋙ overFunctor F) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.comp G F) (CategoryOver.comp G F) =>
              η.toNatTrans) eGF.hom_inv_id)
    · simpa [overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor] using
        (show eGF.inv.toNatTrans ≫ eGF.hom.toNatTrans =
            𝟙 (𝟭 Y.left) from
          congrArg
            (fun η : OverNatTrans (CategoryOver.id Y) (CategoryOver.id Y) =>
              η.toNatTrans) eGF.inv_hom_id)
  constructor
  · intro hX
    let : (structureFunctor X).IsFibered := hX
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro y R f
    let hGy := congrArg (fun K : Y.left ⥤ C => K.obj y) (overFunctor_comm G)
    let fX := f ≫ eqToHom hGy.symm
    obtain ⟨x, φ, hφ⟩ :=
      hX.toIsPreFibered.exists_isCartesian' fX
    let : (structureFunctor X).IsCartesian fX φ := hφ
    let : (structureFunctor X).IsStronglyCartesian fX φ := inferInstance
    have hdom : (structureFunctor X).obj x = R :=
      CategoryTheory.IsHomLift.domain_eq (structureFunctor X) fX φ
    subst R
    have hmap : fX = (structureFunctor X).map φ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift (structureFunctor X) fX φ
    have hφ' : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map φ) φ := by
      simpa [hmap] using
        (inferInstance : (structureFunctor X).IsStronglyCartesian fX φ)
    have hFφ := equivalence_over_preserves_stronglyCartesian F
      ⟨G, ⟨eFG⟩, ⟨eGF⟩⟩ φ hφ'
    let : (structureFunctor Y).IsStronglyCartesian
        ((structureFunctor Y).map ((overFunctor F).map φ)) ((overFunctor F).map φ) := hFφ
    let e := eGF'.hom.app y
    let : IsIso e := by
      change IsIso (eGF'.hom.app y)
      exact NatIso.hom_app_isIso eGF' y
    let : (structureFunctor Y).IsStronglyCartesian
        ((structureFunctor Y).map e) e := by infer_instance
    have hcomp : (structureFunctor Y).IsStronglyCartesian
        ((structureFunctor Y).map ((overFunctor F).map φ) ≫
          (structureFunctor Y).map e)
        ((overFunctor F).map φ ≫ e) := by infer_instance
    let hFGx := congrArg (fun K : X.left ⥤ C => K.obj x) (overFunctor_comm F)
    let hFGy := congrArg (fun K : X.left ⥤ C =>
      K.obj ((overFunctor G).obj y)) (overFunctor_comm F)
    have hFmap : (structureFunctor Y).map ((overFunctor F).map φ) =
        eqToHom hFGx ≫ (structureFunctor X).map φ ≫ eqToHom hFGy.symm := by
      exact Functor.congr_hom (overFunctor_comm F) φ
    have hebase : (structureFunctor Y).map e =
        eqToHom (hFGy.trans hGy) := by
      simpa [e, eGF', overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor, Cat.Hom.id_obj, overIdentityComponent] using
        eGF.hom.over y
    have hf : f = (structureFunctor X).map φ ≫ eqToHom hGy := by
      apply (cancel_mono (eqToHom hGy.symm)).1
      calc
        f ≫ eqToHom hGy.symm = fX := rfl
        _ = (structureFunctor X).map φ := hmap
        _ = ((structureFunctor X).map φ ≫ eqToHom hGy) ≫
            eqToHom hGy.symm := by simp
    have hfcomp : f = eqToHom hFGx.symm ≫
        ((structureFunctor Y).map ((overFunctor F).map φ) ≫
          (structureFunctor Y).map e) := by
      calc
        f = (structureFunctor X).map φ ≫ eqToHom hGy := hf
        _ = eqToHom hFGx.symm ≫
            (eqToHom hFGx ≫ (structureFunctor X).map φ ≫
              eqToHom hFGy.symm) ≫ eqToHom (hFGy.trans hGy) := by
                simp [Category.assoc]
        _ = eqToHom hFGx.symm ≫
            ((structureFunctor Y).map ((overFunctor F).map φ) ≫
              (structureFunctor Y).map e) := by rw [hFmap, hebase]
    let ψ := (overFunctor F).map φ ≫ e
    have hψlift : (structureFunctor Y).IsHomLift f ψ := by
      apply CategoryTheory.IsHomLift.of_fac (structureFunctor Y) f ψ hFGx rfl
      simpa [ψ, Functor.map_comp, Category.assoc] using hfcomp
    let : (structureFunctor Y).IsHomLift f ψ := hψlift
    have hψstrong : (structureFunctor Y).IsStronglyCartesian f ψ := by
      let u := eqToHom hFGx.symm
      let q := (structureFunctor Y).map ((overFunctor F).map φ) ≫
        (structureFunctor Y).map e
      let : (structureFunctor Y).IsStronglyCartesian q ψ := by
        simpa [q, ψ] using hcomp
      constructor
      intro c g τ hτ
      let : (structureFunctor Y).IsHomLift (g ≫ f) τ := hτ
      have hfactor : g ≫ f = (g ≫ u) ≫ q := by
        rw [hfcomp]
        simp [u, q, Category.assoc]
      obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
        Functor.IsStronglyCartesian.universal_property (structureFunctor Y)
          q ψ (g ≫ u) (g ≫ f) hfactor τ
      have hχmap : g ≫ u = (structureFunctor Y).map χ :=
        CategoryTheory.IsHomLift.eq_of_isHomLift
          (structureFunctor Y) (g ≫ u) χ
      have hχbase : (structureFunctor Y).IsHomLift g χ := by
        apply CategoryTheory.IsHomLift.of_fac (structureFunctor Y) g χ rfl hFGx
        rw [← hχmap]
        simp [u, Category.assoc]
      refine ⟨χ, ⟨hχbase, hχeq⟩, ?_⟩
      intro χ' hχ'
      rcases hχ' with ⟨hχ'base, hχ'fac⟩
      let : (structureFunctor Y).IsHomLift g χ' := hχ'base
      have hχ'map : g = (structureFunctor Y).map χ' ≫ eqToHom hFGx := by
        simpa [Category.assoc] using
          (CategoryTheory.IsHomLift.fac (structureFunctor Y) g χ')
      have hχ'comp : (structureFunctor Y).IsHomLift (g ≫ u) χ' := by
        apply CategoryTheory.IsHomLift.of_fac
          (structureFunctor Y) (g ≫ u) χ' rfl rfl
        rw [hχ'map]
        simp [u, Category.assoc]
      exact hχuniq χ' ⟨hχ'comp, hχ'fac⟩
    exact ⟨(overFunctor F).obj x, ψ, hψstrong⟩
  · intro hY
    let : (structureFunctor Y).IsFibered := hY
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro x R f
    let hFx := congrArg (fun K : X.left ⥤ C => K.obj x) (overFunctor_comm F)
    let fY := f ≫ eqToHom hFx.symm
    obtain ⟨y, φ, hφ⟩ := hY.toIsPreFibered.exists_isCartesian' fY
    let : (structureFunctor Y).IsCartesian fY φ := hφ
    let : (structureFunctor Y).IsStronglyCartesian fY φ := inferInstance
    have hdom : (structureFunctor Y).obj y = R :=
      CategoryTheory.IsHomLift.domain_eq (structureFunctor Y) fY φ
    subst R
    have hmap : fY = (structureFunctor Y).map φ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift (structureFunctor Y) fY φ
    have hφ' : (structureFunctor Y).IsStronglyCartesian
        ((structureFunctor Y).map φ) φ := by
      simpa [hmap] using
        (inferInstance : (structureFunctor Y).IsStronglyCartesian fY φ)
    have hGφ := equivalence_over_preserves_stronglyCartesian G
      ⟨F, ⟨eGF⟩, ⟨eFG⟩⟩ φ hφ'
    let : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map ((overFunctor G).map φ)) ((overFunctor G).map φ) := hGφ
    let e := eFG'.hom.app x
    let : IsIso e := by
      change IsIso (eFG'.hom.app x)
      exact NatIso.hom_app_isIso eFG' x
    let : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map e) e := by infer_instance
    have hcomp : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map ((overFunctor G).map φ) ≫
          (structureFunctor X).map e)
        ((overFunctor G).map φ ≫ e) := by infer_instance
    let hGFy := congrArg (fun K : Y.left ⥤ C => K.obj y) (overFunctor_comm G)
    let hGFx := congrArg (fun K : Y.left ⥤ C =>
      K.obj ((overFunctor F).obj x)) (overFunctor_comm G)
    have hGmap : (structureFunctor X).map ((overFunctor G).map φ) =
        eqToHom hGFy ≫ (structureFunctor Y).map φ ≫ eqToHom hGFx.symm := by
      exact Functor.congr_hom (overFunctor_comm G) φ
    have hebase : (structureFunctor X).map e =
        eqToHom (hGFx.trans hFx) := by
      simpa [e, eFG', overFunctor, CategoryOver.comp, CategoryOver.id,
        CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor,
        Cat.Hom.id_toFunctor, Cat.Hom.id_obj, overIdentityComponent] using
        eFG.hom.over x
    have hf : f = (structureFunctor Y).map φ ≫ eqToHom hFx := by
      apply (cancel_mono (eqToHom hFx.symm)).1
      calc
        f ≫ eqToHom hFx.symm = fY := rfl
        _ = (structureFunctor Y).map φ := hmap
        _ = ((structureFunctor Y).map φ ≫ eqToHom hFx) ≫
            eqToHom hFx.symm := by simp
    have hfcomp : f = eqToHom hGFy.symm ≫
        ((structureFunctor X).map ((overFunctor G).map φ) ≫
          (structureFunctor X).map e) := by
      calc
        f = (structureFunctor Y).map φ ≫ eqToHom hFx := hf
        _ = eqToHom hGFy.symm ≫
            (eqToHom hGFy ≫ (structureFunctor Y).map φ ≫
              eqToHom hGFx.symm) ≫ eqToHom (hGFx.trans hFx) := by
                simp [Category.assoc]
        _ = eqToHom hGFy.symm ≫
            ((structureFunctor X).map ((overFunctor G).map φ) ≫
              (structureFunctor X).map e) := by rw [hGmap, hebase]
    let ψ := (overFunctor G).map φ ≫ e
    have hψlift : (structureFunctor X).IsHomLift f ψ := by
      apply CategoryTheory.IsHomLift.of_fac (structureFunctor X) f ψ hGFy rfl
      simpa [ψ, Functor.map_comp, Category.assoc] using hfcomp
    let : (structureFunctor X).IsHomLift f ψ := hψlift
    have hψstrong : (structureFunctor X).IsStronglyCartesian f ψ := by
      let u := eqToHom hGFy.symm
      let q := (structureFunctor X).map ((overFunctor G).map φ) ≫
        (structureFunctor X).map e
      let : (structureFunctor X).IsStronglyCartesian q ψ := by
        simpa [q, ψ] using hcomp
      constructor
      intro c g τ hτ
      let : (structureFunctor X).IsHomLift (g ≫ f) τ := hτ
      have hfactor : g ≫ f = (g ≫ u) ≫ q := by
        rw [hfcomp]
        simp [u, q, Category.assoc]
      obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
        Functor.IsStronglyCartesian.universal_property (structureFunctor X)
          q ψ (g ≫ u) (g ≫ f) hfactor τ
      have hχmap : g ≫ u = (structureFunctor X).map χ :=
        CategoryTheory.IsHomLift.eq_of_isHomLift
          (structureFunctor X) (g ≫ u) χ
      have hχbase : (structureFunctor X).IsHomLift g χ := by
        apply CategoryTheory.IsHomLift.of_fac (structureFunctor X) g χ rfl hGFy
        rw [← hχmap]
        simp [u, Category.assoc]
      refine ⟨χ, ⟨hχbase, hχeq⟩, ?_⟩
      intro χ' hχ'
      rcases hχ' with ⟨hχ'base, hχ'fac⟩
      let : (structureFunctor X).IsHomLift g χ' := hχ'base
      have hχ'map : g = (structureFunctor X).map χ' ≫ eqToHom hGFy := by
        simpa [Category.assoc] using
          (CategoryTheory.IsHomLift.fac (structureFunctor X) g χ')
      have hχ'comp : (structureFunctor X).IsHomLift (g ≫ u) χ' := by
        apply CategoryTheory.IsHomLift.of_fac
          (structureFunctor X) (g ≫ u) χ' rfl rfl
        rw [hχ'map]
        simp [u, Category.assoc]
      exact hχuniq χ' ⟨hχ'comp, hχ'fac⟩
    exact ⟨(overFunctor G).obj y, ψ, hψstrong⟩

/-! ## The 2-fibre product statement -/

/- The iso-comma construction gives a fibre product whose apex is fibred.
   Its projections are fibred morphisms: the componentwise cartesian lift is
   strongly cartesian in the iso-comma, and uniqueness up to a vertical
   isomorphism transfers this to every strongly cartesian product arrow. -/
structure FibredTwoFibreProduct {C : Cat.{v, u}}
    {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  diagram : TwoFibreProductOverDiagram F.underlying G.underlying
  apex_fibred : (diagram.base).IsFibered
  left_preserves : MapsStronglyCartesian
    diagram.base (structureFunctor X.underlying) diagram.left
  right_preserves : MapsStronglyCartesian
    diagram.base (structureFunctor Y.underlying) diagram.right
  is_two_fibre_product :
    IsTwoFibreProductOverDiagram.{v, u, u₁, v₁}
      (F := F.underlying) (G := G.underlying) diagram

theorem fibred_categories_have_two_fibre_products
    {C : Cat.{v, u}} (X Y S : FibredCategoryOver C)
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) :
    Nonempty (FibredTwoFibreProduct F G) := by
  sorry

/-! ## Slices, composites, and fibre products -/

theorem fibred_over_slice
    {X C : Type*} [Category* X] [Category* C]
    (U : C) (p : X ⥤ C) (p' : X ⥤ Over U)
    (factor : p' ⋙ Over.forget U = p) [p.IsFibered] :
    p'.IsFibered := by
  cases factor
  let q := p' ⋙ Over.forget U
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro x R f
  obtain ⟨y, ψ, hψ⟩ :=
    (fibred_category_iff_exists_stronglyCartesian q).mp (inferInstance)
      x R.left f.left
  let : q.IsStronglyCartesian f.left ψ := hψ
  let : q.IsHomLift f.left ψ := by infer_instance
  have hdom : (p'.obj y).left = R.left :=
    CategoryTheory.IsHomLift.domain_eq q f.left ψ
  have hfac' : (p'.map ψ).left = eqToHom hdom ≫ f.left := by
    have h := CategoryTheory.IsHomLift.fac' q f.left ψ
    simpa [q, Category.assoc] using h
  have hobj : p'.obj y = R := by
    apply CostructuredArrow.obj_ext (p'.obj y) R hdom
    calc
      eqToHom hdom ≫ R.hom =
          eqToHom hdom ≫ f.left ≫ (p'.obj x).hom := by
            rw [Over.w f]
      _ = (p'.map ψ).left ≫ (p'.obj x).hom := by
            rw [hfac']
            simp [Category.assoc]
      _ = (p'.obj y).hom := Over.w (p'.map ψ)
  subst R
  have hmap : f.left = (p'.map ψ).left := by
    simpa using hfac'.symm
  have hf : f = p'.map ψ := by
    apply Over.OverMorphism.ext
    exact hmap
  let : p'.IsHomLift f ψ := by
    rw [hf]
    infer_instance
  have hψ' : p'.IsStronglyCartesian f ψ := by
    constructor
    intro z g τ hτ
    let : p'.IsHomLift (g ≫ f) τ := hτ
    have hτmap : g ≫ f = p'.map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p' (g ≫ f) τ
    have hτmap_left : (g ≫ f).left = (p'.map τ).left :=
      congrArg (fun k => k.left) hτmap
    have hτbase : g.left ≫ f.left = q.map τ := by
      simpa [q] using hτmap_left
    have hτq : q.IsHomLift (g.left ≫ f.left) τ := by
      rw [hτbase]
      exact Functor.IsHomLift.map τ
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property q f.left ψ
        g.left (g.left ≫ f.left) rfl τ
    let : (p' ⋙ Over.forget U).IsHomLift g.left χ := hχ
    have hχmap : g.left = (p'.map χ).left := by
      change g.left = (p' ⋙ Over.forget U).map χ
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (p' ⋙ Over.forget U) z y g.left χ hχ
    have hg : g = p'.map χ := by
      apply Over.OverMorphism.ext
      exact hχmap
    let : p'.IsHomLift g χ := by
      rw [hg]
      infer_instance
    refine ⟨χ, ⟨inferInstance, hχfac⟩, ?_⟩
    intro χ' hχ'
    rcases hχ' with ⟨hχ'base, hχ'fac⟩
    let : p'.IsHomLift g χ' := hχ'base
    have hχ'map : g = p'.map χ' :=
      CategoryTheory.IsHomLift.eq_of_isHomLift p' g χ'
    have hχ'map_left : g.left = (p'.map χ').left :=
      congrArg (fun k => k.left) hχ'map
    have hχ'base : g.left = q.map χ' := by
      simpa [q] using hχ'map_left
    have hχ'q : q.IsHomLift g.left χ' := by
      rw [hχ'base]
      exact Functor.IsHomLift.map χ'
    exact hχuniq χ' ⟨hχ'q, hχ'fac⟩
  exact ⟨y, ψ, hψ'⟩

theorem fibred_over_fibred
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (p : A ⥤ B) (q : B ⥤ C) [p.IsFibered] [q.IsFibered] :
    (p ⋙ q).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro a R f
  obtain ⟨b, ψ, hψ⟩ :=
    (fibred_category_iff_exists_stronglyCartesian q).mp (inferInstance)
      (p.obj a) R f
  obtain ⟨a', φ, hφ⟩ :=
    (fibred_category_iff_exists_stronglyCartesian p).mp (inferInstance)
      a b ψ
  let : p.IsStronglyCartesian ψ φ := hφ
  have hdomP : p.obj a' = b :=
    CategoryTheory.IsHomLift.domain_eq p ψ φ
  subst b
  have hψmap : ψ = p.map φ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift p ψ φ
  let : q.IsStronglyCartesian f ψ := hψ
  have hdomQ : q.obj (p.obj a') = R :=
    CategoryTheory.IsHomLift.domain_eq q f ψ
  subst R
  have hfmap : f = q.map ψ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift q f ψ
  have hφ' : p.IsStronglyCartesian (p.map φ) φ := by
    simpa [hψmap] using
      (inferInstance : p.IsStronglyCartesian ψ φ)
  have hψ' : q.IsStronglyCartesian (q.map (p.map φ)) (p.map φ) := by
    simpa [hfmap, hψmap] using
      (inferInstance : q.IsStronglyCartesian f ψ)
  let : p.IsStronglyCartesian (p.map φ) φ := hφ'
  let : q.IsStronglyCartesian (q.map (p.map φ)) (p.map φ) := hψ'
  have hcomp : (p ⋙ q).IsStronglyCartesian ((p ⋙ q).map φ) φ :=
    stronglyCartesian_over_composition p q φ
  have hfcomp : f = (p ⋙ q).map φ := by
    calc
      f = q.map ψ := hfmap
      _ = q.map (p.map φ) := congrArg q.map hψmap
      _ = (p ⋙ q).map φ := by simp only [Functor.comp_map]
  exact ⟨a', φ, by simpa [hfcomp] using hcomp⟩

theorem fibred_fibre_product_goes_up
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered]
    {x y z : X} (f : x ⟶ y) (g : z ⟶ y)
    [Functor.IsStronglyCartesian p (p.map f) f]
    [HasPullback (p.map f) (p.map g)] :
    ∃ (w : X) (a : w ⟶ z) (b : w ⟶ x),
      p.obj w = pullback (p.map f) (p.map g) ∧
        Functor.IsStronglyCartesian p (pullback.snd (p.map f) (p.map g)) a ∧
        IsPullback b a f g := by
  obtain ⟨w, a, ha⟩ :=
    (fibred_category_iff_exists_stronglyCartesian p).mp (inferInstance)
      z (pullback (p.map f) (p.map g)) (pullback.snd (p.map f) (p.map g))
  let : Functor.IsStronglyCartesian p
      (pullback.snd (p.map f) (p.map g)) a := ha
  obtain ⟨b, hb⟩ := stronglyCartesian_fibre_product p f g
    (CategoryTheory.IsPullback.of_hasPullback (p.map f) (p.map g)) w a
  refine ⟨w, a, b, ?_, ha, hb⟩
  exact CategoryTheory.IsHomLift.domain_eq p
    (pullback.snd (p.map f) (p.map g)) a

/-! ## The amelioration factorisation -/

/- The explicit category in the source is the full subcategory of the comma
   category `Comma (𝟭 Y) F` on arrows in a common fibre.  This reuses
   Mathlib's comma and full-subcategory constructors. -/
def ameliorationProperty {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    ObjectProperty (Comma (𝟭 Y.underlying.left) (overFunctor F.underlying)) :=
  fun ξ => ∃ U : C,
    IsObjectLift (structureFunctor Y.underlying) U ξ.left ∧
      IsObjectLift (structureFunctor X.underlying) U ξ.right ∧
        IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.hom

abbrev AmeliorationCategory {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :=
  (ameliorationProperty F).FullSubcategory

/- The source's fully faithful functor `u : X ⥤ X'` sends an object to the
   identity arrow `F(x) ⟶ F(x)` in the comma presentation. -/
def ameliorationFromX {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    X.underlying.left ⥤ AmeliorationCategory F where
  obj x :=
    { obj :=
        { left := (overFunctor F.underlying).obj x
          right := x
          hom := 𝟙 ((overFunctor F.underlying).obj x) }
      property := by
        refine ⟨(structureFunctor X.underlying).obj x, ?_, rfl, ?_⟩
        · exact congrArg (fun K : X.underlying.left ⥤ C => K.obj x)
            (overFunctor_comm F.underlying)
        · exact IsHomLift.id
            (congrArg (fun K : X.underlying.left ⥤ C => K.obj x)
              (overFunctor_comm F.underlying)) }
  map f :=
    ObjectProperty.homMk
      { left := (overFunctor F.underlying).map f
        right := f
        w := by simp }
  map_id := by
    intro x
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp
  map_comp := by
    intro x y z f g
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext <;> simp

theorem amelioration_object_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) (ξ : AmeliorationCategory F) :
    ∃ U : C,
      IsObjectLift (structureFunctor Y.underlying) U ξ.obj.left ∧
        IsObjectLift (structureFunctor X.underlying) U ξ.obj.right ∧
          IsMorphismLift (structureFunctor Y.underlying) (𝟙 U) ξ.obj.hom :=
  ξ.property

theorem amelioration_morphism_description
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y)
    {ξ ξ' : AmeliorationCategory F} (h : ξ ⟶ ξ') :
    h.hom.left ≫ ξ'.obj.hom =
      ξ.obj.hom ≫ (overFunctor F.underlying).map h.hom.right := by
  exact h.hom.w

def ameliorationToX {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ X.underlying.left :=
  (ameliorationProperty F).ι ⋙ Comma.snd (𝟭 Y.underlying.left)
    (overFunctor F.underlying)

def ameliorationToY {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ Y.underlying.left :=
  (ameliorationProperty F).ι ⋙ Comma.fst (𝟭 Y.underlying.left)
    (overFunctor F.underlying)

/- The explicit comma presentation carries a canonical functor to the fixed
   base via its `Y`-projection.  The source proof shows that this functor is
   fibred, even though the comma category can live in a larger universe than
   the bundled `CategoryOver` carrier. -/
def ameliorationBase {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    AmeliorationCategory F ⥤ C :=
  ameliorationToY F ⋙ structureFunctor Y.underlying

theorem ameliorationBase_isFibred {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    (ameliorationBase F).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro ξ R f
  change R ⟶ (structureFunctor Y.underlying).obj ξ.obj.left at f
  rcases ξ.property with ⟨U, hY, hX, hξ⟩
  subst U
  change (structureFunctor X.underlying).obj ξ.obj.right =
      (structureFunctor Y.underlying).obj ξ.obj.left at hX
  let fX : R ⟶ (structureFunctor X.underlying).obj ξ.obj.right :=
    f ≫ eqToHom hX.symm
  obtain ⟨x', b, hb⟩ :=
      (fibred_category_iff_exists_stronglyCartesian
      (structureFunctor X.underlying)).mp (inferInstance)
      ξ.obj.right R fX
  let : (structureFunctor X.underlying).IsStronglyCartesian fX b := hb
  obtain ⟨y', a, ha⟩ :=
    (fibred_category_iff_exists_stronglyCartesian
      (structureFunctor Y.underlying)).mp (inferInstance)
      ξ.obj.left R f
  let : (structureFunctor Y.underlying).IsStronglyCartesian f a := ha
  have hdomX : (structureFunctor X.underlying).obj x' = R :=
    CategoryTheory.IsHomLift.domain_eq (structureFunctor X.underlying) fX b
  subst R
  have hBmap : fX = (structureFunctor X.underlying).map b :=
    CategoryTheory.IsHomLift.eq_of_isHomLift
      (structureFunctor X.underlying) fX b
  have hb' : (structureFunctor X.underlying).IsStronglyCartesian
      ((structureFunctor X.underlying).map b) b := by
    simpa [hBmap] using hb
  have hFstrong := F.preserves b hb'
  let : (structureFunctor Y.underlying).IsStronglyCartesian
      ((structureFunctor Y.underlying).map
        ((overFunctor F.underlying).map b))
      ((overFunctor F.underlying).map b) := hFstrong
  let : (structureFunctor Y.underlying).IsHomLift
      (𝟙 ((structureFunctor Y.underlying).obj ξ.obj.left)) ξ.obj.hom := hξ
  have hcomp : (structureFunctor Y.underlying).IsHomLift f
      (a ≫ ξ.obj.hom) := by
    exact IsHomLift.comp_lift_id_right'
      (structureFunctor Y.underlying) f a
      ((structureFunctor Y.underlying).obj ξ.obj.left) ξ.obj.hom
  have hdomY : (structureFunctor Y.underlying).obj y' =
      (structureFunctor X.underlying).obj x' :=
    CategoryTheory.IsHomLift.domain_eq
      (structureFunctor Y.underlying) f a
  let hFx' := congrArg (fun K : X.underlying.left ⥤ C => K.obj x')
    (overFunctor_comm F.underlying)
  let hFx := congrArg (fun K : X.underlying.left ⥤ C =>
    K.obj ξ.obj.right) (overFunctor_comm F.underlying)
  have hFmap : (structureFunctor Y.underlying).map
      ((overFunctor F.underlying).map b) =
      eqToHom hFx' ≫ (structureFunctor X.underlying).map b ≫
        eqToHom hFx.symm := by
    exact Functor.congr_hom (overFunctor_comm F.underlying) b
  have hmapA : (structureFunctor Y.underlying).map a =
      eqToHom hdomY ≫ f := by
    simpa using
      (CategoryTheory.IsHomLift.fac'
        (structureFunctor Y.underlying) f a)
  let hcodξ := CategoryTheory.IsHomLift.codomain_eq
    (structureFunctor Y.underlying)
    (𝟙 ((structureFunctor Y.underlying).obj ξ.obj.left)) ξ.obj.hom
  have hmapξ : (structureFunctor Y.underlying).map ξ.obj.hom =
      eqToHom hcodξ.symm := by
    simpa using
      (CategoryTheory.IsHomLift.fac'
        (structureFunctor Y.underlying)
        (𝟙 ((structureFunctor Y.underlying).obj ξ.obj.left)) ξ.obj.hom)
  have hcodξ_eq : hcodξ = hFx.trans hX := Subsingleton.elim _ _
  let hsource := hdomY.trans hFx'.symm
  have hfactor : (structureFunctor Y.underlying).map (a ≫ ξ.obj.hom) =
      eqToHom hsource ≫
        (structureFunctor Y.underlying).map
          ((overFunctor F.underlying).map b) := by
    rw [Functor.map_comp, hmapA, hmapξ, hFmap, ← hBmap]
    dsimp [hsource, fX]
    simp [Category.assoc]
  obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      (structureFunctor Y.underlying)
      ((structureFunctor Y.underlying).map
        ((overFunctor F.underlying).map b))
      ((overFunctor F.underlying).map b) (eqToHom hsource)
      ((structureFunctor Y.underlying).map (a ≫ ξ.obj.hom)) hfactor
      (a ≫ ξ.obj.hom)
  have hχmap : eqToHom hsource =
      (structureFunctor Y.underlying).map χ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift
      (structureFunctor Y.underlying) (eqToHom hsource) χ
  let hcodχ := hFx'
  have hχvertical : (structureFunctor Y.underlying).IsHomLift
      (𝟙 ((structureFunctor X.underlying).obj x')) χ := by
    apply CategoryTheory.IsHomLift.of_fac
      (structureFunctor Y.underlying) (𝟙 ((structureFunctor X.underlying).obj x'))
      χ hdomY hcodχ
    rw [← hχmap]
    dsimp [hsource]
    simp
  let η : AmeliorationCategory F :=
    { obj :=
        { left := y'
          right := x'
          hom := χ }
      property := by
        refine ⟨(structureFunctor X.underlying).obj x', hdomY, rfl, ?_⟩
        · exact hχvertical }
  let φ : η ⟶ ξ :=
    ObjectProperty.homMk
      { left := a
        right := b
        w := hχeq.symm }
  have hdomη : (ameliorationBase F).obj η =
      (structureFunctor X.underlying).obj x' := hdomY
  have hcodξbase : (ameliorationBase F).obj ξ =
      (structureFunctor Y.underlying).obj ξ.obj.left := rfl
  have hcodξbase_eq : hcodξbase = rfl := Subsingleton.elim _ _
  refine ⟨η, φ, ?_⟩
  let hbase : (ameliorationBase F).IsHomLift f φ := by
    apply CategoryTheory.IsHomLift.of_fac
      (ameliorationBase F) f φ
      (by
        change (structureFunctor Y.underlying).obj y' =
          (structureFunctor X.underlying).obj x'
        exact hdomY) hcodξbase
    dsimp [ameliorationBase, ameliorationToY, φ, Comma.fst,
      ObjectProperty.homMk]
    rw [hmapA]
    rw [hcodξbase_eq]
    change f = eqToHom hdomY.symm ≫ (eqToHom hdomY ≫ f) ≫
      eqToHom (rfl : (structureFunctor Y.underlying).obj ξ.obj.left =
        (structureFunctor Y.underlying).obj ξ.obj.left)
    simp
  refine { toIsHomLift := hbase, universal_property' := ?_ }
  intro ζ g τ hτ
  let : (ameliorationBase F).IsHomLift (g ≫ f) τ := hτ
  have hτY : (structureFunctor Y.underlying).IsHomLift
      (g ≫ f) τ.hom.left := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor Y.underlying) (g ≫ f) τ.hom.left rfl rfl
    have hfac := CategoryTheory.IsHomLift.fac'
      (ameliorationBase F) (g ≫ f) τ
    dsimp [ameliorationBase, ameliorationToY] at hfac
    exact hfac
  let : (structureFunctor Y.underlying).IsHomLift (g ≫ f) τ.hom.left := hτY
  obtain ⟨χleft, ⟨hχleft, hχleftfac⟩, hχleftuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      (structureFunctor Y.underlying) f a g (g ≫ f) rfl τ.hom.left
  rcases ζ.property with ⟨Uζ, hζY, hζX, hζhom⟩
  subst Uζ
  change (structureFunctor X.underlying).obj ζ.obj.right =
      (structureFunctor Y.underlying).obj ζ.obj.left at hζX
  change (structureFunctor Y.underlying).obj ζ.obj.left ⟶
      (structureFunctor X.underlying).obj x' at g
  let gX : (structureFunctor X.underlying).obj ζ.obj.right ⟶
      (structureFunctor X.underlying).obj x' :=
    eqToHom hζX ≫ g
  let : (structureFunctor Y.underlying).IsHomLift
      (𝟙 ((structureFunctor Y.underlying).obj ζ.obj.left)) ζ.obj.hom := hζhom
  have hFζ :
      (overFunctor F.underlying ⋙ structureFunctor Y.underlying).obj ζ.obj.right =
        (structureFunctor X.underlying).obj ζ.obj.right :=
    congrArg (fun K => K.obj ζ.obj.right) (overFunctor_comm F.underlying)
  have hζmap :
      (structureFunctor Y.underlying).map ζ.obj.hom =
        eqToHom (hFζ.trans hζX).symm := by
    have hd := CategoryTheory.IsHomLift.domain_eq
      (structureFunctor Y.underlying)
      (𝟙 ((structureFunctor Y.underlying).obj ζ.obj.left)) ζ.obj.hom
    have hc := CategoryTheory.IsHomLift.codomain_eq
      (structureFunctor Y.underlying)
      (𝟙 ((structureFunctor Y.underlying).obj ζ.obj.left)) ζ.obj.hom
    have hd_eq : hd = (rfl :
        (structureFunctor Y.underlying).obj ζ.obj.left =
          (structureFunctor Y.underlying).obj ζ.obj.left) := Subsingleton.elim _ _
    have hc_eq : hc = hFζ.trans hζX := Subsingleton.elim _ _
    have hfac := CategoryTheory.IsHomLift.fac'
      (structureFunctor Y.underlying)
      (𝟙 ((structureFunctor Y.underlying).obj ζ.obj.left)) ζ.obj.hom
    simpa only [Category.id_comp, Category.comp_id, eqToHom_refl, eqToHom_trans] using hfac
  let : (structureFunctor Y.underlying).IsHomLift (g ≫ f) τ.hom.left := hτY
  have hτmapY : g ≫ f =
      (structureFunctor Y.underlying).map τ.hom.left := by
    exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
      (structureFunctor Y.underlying) _ _ (g ≫ f) τ.hom.left hτY
  have hFτ := Functor.congr_hom
    (overFunctor_comm F.underlying) τ.hom.right
  have hτwmap :
      (structureFunctor Y.underlying).map τ.hom.left ≫
          (structureFunctor Y.underlying).map ξ.obj.hom =
        (structureFunctor Y.underlying).map ζ.obj.hom ≫
          (structureFunctor Y.underlying).map
            ((overFunctor F.underlying).map τ.hom.right) := by
    rw [← (structureFunctor Y.underlying).map_comp,
      ← (structureFunctor Y.underlying).map_comp]
    exact congrArg (structureFunctor Y.underlying).map τ.hom.w
  have hτX : (structureFunctor X.underlying).IsHomLift
      (gX ≫ fX) τ.hom.right := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor X.underlying) (gX ≫ fX) τ.hom.right
      rfl rfl
    dsimp [gX, fX]
    rw [← hτmapY, hmapξ, hζmap] at hτwmap
    rw [← Functor.comp_map] at hτwmap
    rw [hFτ] at hτwmap
    have hAB :
        eqToHom (hFζ.trans hζX).symm ≫ eqToHom hFζ =
          eqToHom hζX.symm := by
      rw [eqToHom_trans]
    have hCD :
        eqToHom hX.symm ≫ eqToHom hFx.symm = eqToHom hcodξ.symm := by
      rw [eqToHom_trans]
    have hτwmap' :
        g ≫ f ≫ eqToHom hcodξ.symm =
          eqToHom hζX.symm ≫
            (structureFunctor X.underlying).map τ.hom.right ≫
              eqToHom hFx.symm := by
      calc
        g ≫ f ≫ eqToHom hcodξ.symm =
            eqToHom (hFζ.trans hζX).symm ≫ eqToHom hFζ ≫
              (structureFunctor X.underlying).map τ.hom.right ≫
                eqToHom hFx.symm := by
          simpa only [Category.assoc] using hτwmap
        _ = eqToHom hζX.symm ≫
            (structureFunctor X.underlying).map τ.hom.right ≫
              eqToHom hFx.symm := by
          rw [← Category.assoc, hAB]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_epi (eqToHom hζX.symm)).1
    apply (cancel_mono (eqToHom hFx.symm)).1
    simp only [Category.assoc]
    rw [← hτwmap']
    rw [← Category.assoc]
    simp
  let : (structureFunctor X.underlying).IsHomLift
      (gX ≫ fX) τ.hom.right := hτX
  obtain ⟨χright, ⟨hχright, hχrightfac⟩, hχrightuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property
      (structureFunctor X.underlying) fX b gX (gX ≫ fX) rfl τ.hom.right
  have hFmapχright :
      (structureFunctor Y.underlying).map
          ((overFunctor F.underlying).map χright) =
        eqToHom hFζ ≫ (structureFunctor X.underlying).map χright ≫
          eqToHom hFx'.symm := by
    exact Functor.congr_hom (overFunctor_comm F.underlying) χright
  have hχrightmap : gX =
      (structureFunctor X.underlying).map χright := by
    exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
      (structureFunctor X.underlying) _ _ gX χright hχright
  have hFχright : (structureFunctor Y.underlying).IsHomLift g
      ((overFunctor F.underlying).map χright) := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor Y.underlying) g
      ((overFunctor F.underlying).map χright)
      (hFζ.trans hζX) hFx'
    rw [hFmapχright, ← hχrightmap]
    dsimp [gX]
    simp [Category.assoc]
  let : (structureFunctor Y.underlying).IsHomLift
      (𝟙 ((structureFunctor Y.underlying).obj ζ.obj.left)) ζ.obj.hom := hζhom
  let : (structureFunctor Y.underlying).IsHomLift g
      ((overFunctor F.underlying).map χright) := hFχright
  have hrightcomp : (structureFunctor Y.underlying).IsHomLift g
      (ζ.obj.hom ≫ (overFunctor F.underlying).map χright) :=
    IsHomLift.comp_lift_id_left'
      (structureFunctor Y.underlying)
      ((structureFunctor Y.underlying).obj ζ.obj.left) ζ.obj.hom g
      ((overFunctor F.underlying).map χright)
  let : (structureFunctor Y.underlying).IsHomLift g χleft := hχleft
  let : (structureFunctor Y.underlying).IsHomLift
      (𝟙 ((structureFunctor X.underlying).obj x')) χ := hχvertical
  have hleftcomp : (structureFunctor Y.underlying).IsHomLift g
      (χleft ≫ χ) :=
    IsHomLift.comp_lift_id_right'
      (structureFunctor Y.underlying) g χleft
      ((structureFunctor X.underlying).obj x') χ
  let g' : (structureFunctor Y.underlying).obj ζ.obj.left ⟶
      (overFunctor F.underlying ⋙ structureFunctor Y.underlying).obj x' :=
    g ≫ eqToHom hFx'.symm
  have hleftcomp' : (structureFunctor Y.underlying).IsHomLift g'
      (χleft ≫ χ) := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor Y.underlying) g' (χleft ≫ χ) rfl rfl
    have hfac := CategoryTheory.IsHomLift.fac'
      (structureFunctor Y.underlying) g (χleft ≫ χ)
    dsimp [g']
    simpa [Category.assoc] using hfac
  have hrightcomp' : (structureFunctor Y.underlying).IsHomLift g'
      (ζ.obj.hom ≫ (overFunctor F.underlying).map χright) := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor Y.underlying) g'
      (ζ.obj.hom ≫ (overFunctor F.underlying).map χright) rfl rfl
    have hfac := CategoryTheory.IsHomLift.fac'
      (structureFunctor Y.underlying) g
      (ζ.obj.hom ≫ (overFunctor F.underlying).map χright)
    dsimp [g']
    simpa [Category.assoc] using hfac
  have hκw : χleft ≫ χ =
      ζ.obj.hom ≫ (overFunctor F.underlying).map χright := by
    apply Functor.IsStronglyCartesian.ext
      (structureFunctor Y.underlying)
      ((structureFunctor Y.underlying).map
        ((overFunctor F.underlying).map b))
      ((overFunctor F.underlying).map b) g'
    calc
      (χleft ≫ χ) ≫ (overFunctor F.underlying).map b =
          χleft ≫ (χ ≫ (overFunctor F.underlying).map b) := by
            simp [Category.assoc]
      _ = χleft ≫ (a ≫ ξ.obj.hom) := by rw [hχeq]
      _ = τ.hom.left ≫ ξ.obj.hom := by
        simpa only [Category.assoc] using
          congrArg (fun k => k ≫ ξ.obj.hom) hχleftfac
      _ = ζ.obj.hom ≫ (overFunctor F.underlying).map τ.hom.right :=
        τ.hom.w
      _ = ζ.obj.hom ≫
          (overFunctor F.underlying).map
            (χright ≫ b) := by rw [hχrightfac]
      _ = (ζ.obj.hom ≫ (overFunctor F.underlying).map χright) ≫
          (overFunctor F.underlying).map b := by
            simp [Functor.map_comp, Category.assoc]
  let κ : ζ ⟶ η :=
    ObjectProperty.homMk
      { left := χleft
        right := χright
        w := hκw }
  have hκbase : (ameliorationBase F).IsHomLift g κ := by
    apply CategoryTheory.IsHomLift.of_fac'
      (ameliorationBase F) g κ rfl hdomY
    have hfac := CategoryTheory.IsHomLift.fac'
      (structureFunctor Y.underlying) g χleft
    dsimp [ameliorationBase, ameliorationToY, κ,
      ObjectProperty.homMk] at hfac ⊢
    exact hfac
  have hκfac : κ ≫ φ = τ := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · dsimp [κ, φ, ObjectProperty.homMk]
      exact hχleftfac
    · dsimp [κ, φ, ObjectProperty.homMk]
      exact hχrightfac
  refine ⟨κ, ⟨hκbase, hκfac⟩, ?_⟩
  intro m hm
  rcases hm with ⟨hmBase, hmFac⟩
  let : (ameliorationBase F).IsHomLift g m := hmBase
  have hmLeft : (structureFunctor Y.underlying).IsHomLift g m.hom.left := by
    apply CategoryTheory.IsHomLift.of_fac'
      (structureFunctor Y.underlying) g m.hom.left rfl hdomY
    have hfac := CategoryTheory.IsHomLift.fac'
      (ameliorationBase F) g m
    dsimp [ameliorationBase, ameliorationToY] at hfac ⊢
    exact hfac
  have hmLeftFac : m.hom.left ≫ a = τ.hom.left := by
    have hh := congrArg (fun k => k.hom.left) hmFac
    simpa [φ, ObjectProperty.homMk] using hh
  have hmLeftEq : m.hom.left = χleft :=
    hχleftuniq m.hom.left ⟨hmLeft, hmLeftFac⟩
  have hmLeftMap :
      (structureFunctor Y.underlying).map m.hom.left =
        g ≫ eqToHom hdomY.symm := by
    let : (structureFunctor Y.underlying).IsHomLift g m.hom.left := hmLeft
    have hfac := CategoryTheory.IsHomLift.fac'
      (structureFunctor Y.underlying) g m.hom.left
    simpa [Category.assoc] using hfac
  have hmFmap :
      (structureFunctor Y.underlying).map
          ((overFunctor F.underlying).map m.hom.right) =
        eqToHom hFζ ≫ (structureFunctor X.underlying).map m.hom.right ≫
          eqToHom hFx'.symm := by
    exact Functor.congr_hom (overFunctor_comm F.underlying) m.hom.right
  have hmWmap :
      (structureFunctor Y.underlying).map m.hom.left ≫
          (structureFunctor Y.underlying).map χ =
        (structureFunctor Y.underlying).map ζ.obj.hom ≫
          (structureFunctor Y.underlying).map
            ((overFunctor F.underlying).map m.hom.right) := by
    rw [← (structureFunctor Y.underlying).map_comp,
      ← (structureFunctor Y.underlying).map_comp]
    exact congrArg (structureFunctor Y.underlying).map m.hom.w
  rw [hmLeftMap, ← hχmap, hζmap, hmFmap] at hmWmap
  have hmWmap' :
      g ≫ eqToHom hFx'.symm =
        eqToHom hζX.symm ≫
          (structureFunctor X.underlying).map m.hom.right ≫
            eqToHom hFx'.symm := by
    have hmAB :
        eqToHom (hFζ.trans hζX).symm ≫ eqToHom hFζ =
          eqToHom hζX.symm := by
      rw [eqToHom_trans]
    simpa [hsource, Category.assoc, hmAB] using hmWmap
  have hmXMap :
      (structureFunctor X.underlying).map m.hom.right = gX := by
    have hmEq :
        g = eqToHom hζX.symm ≫
          (structureFunctor X.underlying).map m.hom.right := by
      apply (cancel_mono (eqToHom hFx'.symm)).1
      simpa [Category.assoc] using hmWmap'
    apply (cancel_epi (eqToHom hζX.symm)).1
    dsimp [gX]
    simpa [Category.assoc] using hmEq.symm
  have hmRight : (structureFunctor X.underlying).IsHomLift gX m.hom.right := by
    rw [← hmXMap]
    infer_instance
  have hmRightFac : m.hom.right ≫ b = τ.hom.right := by
    have hh := congrArg (fun k => k.hom.right) hmFac
    simpa [φ, ObjectProperty.homMk] using hh
  have hmRightEq : m.hom.right = χright :=
    hχrightuniq m.hom.right ⟨hmRight, hmRightFac⟩
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · simpa [κ, ObjectProperty.homMk] using hmLeftEq
  · simpa [κ, ObjectProperty.homMk] using hmRightEq

/- The three projections and their comparison maps are packaged using raw
   functors.  The comma middle category can have larger universes than the
   fixed `CategoryOver` carrier over `C`, so bundling it as a
   `FibredCategoryOver C` would reject the canonical construction. -/
structure AmeliorationFactorization
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  middle_isFibred : (ameliorationBase F).IsFibered
  u : X.underlying.left ⥤ AmeliorationCategory F
  u_over : u ⋙ ameliorationBase F = structureFunctor X.underlying
  u_preserves : MapsStronglyCartesian
    (structureFunctor X.underlying) (ameliorationBase F) u
  v : AmeliorationCategory F ⥤ Y.underlying.left
  v_over : v ⋙ structureFunctor Y.underlying = ameliorationBase F
  v_preserves : MapsStronglyCartesian
    (ameliorationBase F) (structureFunctor Y.underlying) v
  w : AmeliorationCategory F ⥤ X.underlying.left
  w_over : w ⋙ structureFunctor X.underlying = ameliorationBase F
  w_preserves : MapsStronglyCartesian
    (ameliorationBase F) (structureFunctor X.underlying) w
  factorization : overFunctor F.underlying = u ⋙ v
  u_fully_faithful : Nonempty u.FullyFaithful
  w_left_adjoint_u : Nonempty (w ⊣ u)
  v_fibred_over_Y : v.IsFibered

theorem ameliorate_fibred_morphism
    {C : Cat.{v, u}} (X Y : FibredCategoryOver C)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (AmeliorationFactorization F) := by
  sorry

end

end Formalization.Books.Categories.Unit33
