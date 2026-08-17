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
  letI : (F ⋙ G).IsHomLift (g ≫ (F ⋙ G).map φ) τ := hτ
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
  haveI : (F ⋙ G).IsHomLift g δ := by
    rw [hmap]
    infer_instance
  refine ⟨δ, ⟨inferInstance, hδeq⟩, ?_⟩
  intro δ' ⟨hδ'base, hδ'eq⟩
  have hδ'comp : g = G.map (F.map δ') :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (F ⋙ G) g δ'
  letI : G.IsHomLift g (F.map δ') := by
    rw [hδ'comp]
    infer_instance
  have hFδ' : F.map δ' = χ :=
    hχuniq (F.map δ') ⟨inferInstance, by
      simpa [Functor.comp_map] using congrArg F.map hδ'eq⟩
  letI : F.IsHomLift χ δ' := by
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
  letI : p.IsHomLift (π₁ ≫ p.map f) (a ≫ g) := by
    rw [hP.w]
    infer_instance
  let b : w ⟶ x :=
    Functor.IsStronglyCartesian.map p (p.map f) f
      (f' := π₁ ≫ p.map f) (g := π₁) rfl (a ≫ g)
  have hb : b ≫ f = a ≫ g := by
    dsimp [b]
    simp
  haveI : p.IsHomLift π₁ b := by
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
    letI : p.IsHomLift (p.map u) v := by
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
    letI : p.IsHomLift (k ≫ π₂) s := by
      rw [hk₂]
      infer_instance
    obtain ⟨t, ⟨ht, hta⟩, _⟩ :=
      Functor.IsStronglyCartesian.universal_property p π₂ a k
        (p.map s) hk₂.symm s
    letI := ht
    have htb : t ≫ b = r := by
      have hcomp : (t ≫ b) ≫ f = r ≫ f := by
        calc
          (t ≫ b) ≫ f = t ≫ (b ≫ f) := by simp [Category.assoc]
          _ = t ≫ (a ≫ g) := by rw [hb]
          _ = (t ≫ a) ≫ g := by simp [Category.assoc]
          _ = s ≫ g := by rw [hta]
          _ = r ≫ f := hrs.symm
      haveI : p.IsHomLift (k ≫ π₁) (t ≫ b) := by
        infer_instance
      letI : p.IsHomLift (k ≫ π₁) r := by
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
    haveI : p.IsHomLift (𝟙 S) (𝟙 x.1) := IsHomLift.id x.2
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ (𝟙 x.1)) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S (𝟙 x.1)
    letI : p.IsHomLift f (P.pullbackMap f x ≫ (𝟙 x.1)) := hφ'
    have hpull : p.obj (Functor.Fiber.fiberInclusion.obj (P.pullback f x)) = R :=
      (P.pullback f x).2
    change
      Functor.IsStronglyCartesian.map p f (P.pullbackMap f x)
          (f' := f) (g := 𝟙 R) (by simp)
          (P.pullbackMap f x ≫ (𝟙 x.1)) =
        𝟙 ((P.pullback f x).1)
    letI : p.IsHomLift (𝟙 R) (𝟙 ((P.pullback f x).1)) :=
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
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f y) :=
      P.pullbackMap_isStronglyCartesian f y
    letI : Functor.IsStronglyCartesian p f (P.pullbackMap f z) :=
      P.pullbackMap_isStronglyCartesian f z
    haveI : p.IsHomLift (𝟙 S) φ.1 := φ.2
    haveI : p.IsHomLift (𝟙 S) ψ.1 := ψ.2
    haveI : p.IsHomLift (𝟙 S) (φ ≫ ψ).1 := (φ ≫ ψ).2
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
    letI : p.IsHomLift (𝟙 R) mφ := hmφ
    letI : p.IsHomLift (𝟙 R) mψ := hmψ
    have hmcomp : p.IsHomLift (𝟙 R) (mφ ≫ mψ) := by infer_instance
    change mcomp = mφ ≫ mψ
    letI : p.IsHomLift (𝟙 R) (mφ ≫ mψ) := hmcomp
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
    letI : p.IsHomLift (𝟙 U) eX.hom := by
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
              simp [hx]
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
              simp [hpb₀, pb, hf]
            rw [hpbm]
            letI : p.IsStronglyCartesian (𝟙 S)
                (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀)) :=
              hfiberIsoStrong hpb₀
            letI : p.IsStronglyCartesian f (P₀.pullbackMap f x) :=
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
            simp [hpb₀, pb, hRS]
          rw [hpbm]
          letI : p.IsStronglyCartesian (𝟙 R)
              (Functor.Fiber.fiberInclusion.map (eqToHom hpb₀)) :=
            hfiberIsoStrong hpb₀
          letI : p.IsStronglyCartesian f (P₀.pullbackMap f x) :=
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
    letI : p.IsHomLift (𝟙 B) φ.1 := φ.2
    letI : p.IsStronglyCartesian h (P.pullbackMap h y) :=
      P.pullbackMap_isStronglyCartesian h y
    letI : p.IsStronglyCartesian h (P.pullbackMap h x) :=
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
      letI : p.IsHomLift (𝟙 R) (hom ≫ inv) := by infer_instance
      letI : p.IsHomLift (𝟙 R)
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
      letI : p.IsHomLift (𝟙 R) (inv ≫ hom) := by infer_instance
      letI : p.IsHomLift (𝟙 R)
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
    letI : p.IsStronglyCartesian f (P.pullbackMap f (P.pullback g z)) :=
      P.pullbackMap_isStronglyCartesian f (P.pullback g z)
    letI : p.IsStronglyCartesian g (P.pullbackMap g z) :=
      P.pullbackMap_isStronglyCartesian g z
    letI : p.IsStronglyCartesian (f ≫ g)
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
      letI : p.IsStronglyCartesian f (P.pullbackMap f (P.pullback g y)) :=
        P.pullbackMap_isStronglyCartesian f (P.pullback g y)
      letI : p.IsStronglyCartesian g (P.pullbackMap g y) :=
        P.pullbackMap_isStronglyCartesian g y
      letI : p.IsStronglyCartesian (f ≫ g)
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
        letI : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map mfg) := mfg.2
        letI : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map (component y).hom) :=
          by
            change p.IsHomLift (𝟙 R) (component y).hom.1
            exact (component y).hom.2
        infer_instance
      have hR : p.IsHomLift (𝟙 R)
          (Functor.Fiber.fiberInclusion.map rhs) := by
        letI : p.IsHomLift (𝟙 R)
            (Functor.Fiber.fiberInclusion.map (component x).hom) :=
          by
            change p.IsHomLift (𝟙 R) (component x).hom.1
            exact (component x).hom.2
        letI : p.IsHomLift (𝟙 R)
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
      letI : p.IsHomLift (𝟙 R) lhs.1 := hL'
      letI : p.IsHomLift (𝟙 R) rhs.1 := hR'
      letI : p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map lhs) := hL
      letI : p.IsHomLift (𝟙 R) (Functor.Fiber.fiberInclusion.map rhs) := hR
      have hEq : lhs.1 ≫ P.pullbackMap f (P.pullback g y) ≫
            P.pullbackMap g y = rhs.1 ≫ P.pullbackMap f (P.pullback g y) ≫
            P.pullbackMap g y := by
        dsimp [lhs, rhs]
        calc
        mfg.1 ≫ (component y).hom.1 ≫
              P.pullbackMap f (P.pullback g y) ≫ P.pullbackMap g y =
            mfg.1 ≫ P.pullbackMap (f ≫ g) y := by
              simpa only [Category.assoc] using
                congrArg (fun k => mfg.1 ≫ k) (component_fac y)
        _ = P.pullbackMap (f ≫ g) x ≫ φ.1 := hfg
        _ = (component x).hom.1 ≫
              P.pullbackMap f (P.pullback g x) ≫
              P.pullbackMap g x ≫ φ.1 := by rw [component_fac x]
        _ = (component x).hom.1 ≫
              (mfx.1 ≫ P.pullbackMap f (P.pullback g y)) ≫
              P.pullbackMap g y := by rw [← hf, ← hg]
        _ = (component x).hom.1 ≫ mfx.1 ≫
              P.pullbackMap f (P.pullback g y) ≫
              P.pullbackMap g y := by simp [Category.assoc]
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
    letI : p.IsStronglyCartesian (f ≫ g)
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
    letI : p.IsHomLift (𝟙 R) (β.hom.app x).1 := hβlift'
    letI : p.IsHomLift (𝟙 R) (α.hom.app x).1 := hαlift'
    letI : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x)) := hβlift
    letI : p.IsHomLift (𝟙 R)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x)) := hαlift
    have hEq : (β.hom.app x).1 ≫ P.pullbackMap f (P.pullback g x) ≫
          P.pullbackMap g x = (α.hom.app x).1 ≫
          P.pullbackMap f (P.pullback g x) ≫ P.pullbackMap g x := by
      calc
        (β.hom.app x).1 ≫ P.pullbackMap f (P.pullback g x) ≫
            P.pullbackMap g x = P.pullbackMap (f ≫ g) x := by
              have hβx := hβ x
              change (β.hom.app x).1 ≫ P.pullbackMap f
                (P.pullback g x) ≫ P.pullbackMap g x =
                  P.pullbackMap (f ≫ g) x at hβx
              exact hβx
        _ = (α.hom.app x).1 ≫ P.pullbackMap f (P.pullback g x) ≫
            P.pullbackMap g x := by
              exact (component_fac x).symm
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
  classical
  let component : ∀ x : Functor.Fiber p U,
      x ≅ P.pullback (𝟙 U) x := by
    intro x
    letI : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    letI : p.IsStronglyCartesian (𝟙 U) (𝟙 x.1) :=
      iso_is_stronglyCartesian p (𝟙 U) (Iso.refl x.1)
    letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    let hom : x.1 ⟶ (P.pullback (𝟙 U) x).1 :=
      @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (𝟙 U)
        (P.pullbackMap (𝟙 U) x) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (𝟙 x.1) (by infer_instance)
    have hom_lift : p.IsHomLift (𝟙 U) hom := by
      dsimp [hom]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _
        (𝟙 U) (P.pullbackMap (𝟙 U) x) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (𝟙 x.1) (by infer_instance)
    have hom_fac : hom ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
      dsimp [hom]
      exact Functor.IsStronglyCartesian.fac p (𝟙 U)
        (P.pullbackMap (𝟙 U) x) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
        (𝟙 x.1)
    let homF : x ⟶ P.pullback (𝟙 U) x := ⟨hom, hom_lift⟩
    let invF : P.pullback (𝟙 U) x ⟶ x :=
      ⟨P.pullbackMap (𝟙 U) x, by infer_instance⟩
    refine { hom := homF, inv := invF, hom_inv_id := ?_, inv_hom_id := ?_ }
    · apply Functor.Fiber.hom_ext
      change hom ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
      exact hom_fac
    · apply Functor.Fiber.hom_ext
      change P.pullbackMap (𝟙 U) x ≫ hom = 𝟙 _
      letI : p.IsHomLift (𝟙 U)
          (P.pullbackMap (𝟙 U) x ≫ hom) := by infer_instance
      letI : p.IsHomLift (𝟙 U)
          (𝟙 ((P.pullback (𝟙 U) x).1)) :=
        IsHomLift.id (P.pullback (𝟙 U) x).2
      apply Functor.IsStronglyCartesian.ext p (𝟙 U)
        (P.pullbackMap (𝟙 U) x) (𝟙 U)
      calc
        (P.pullbackMap (𝟙 U) x ≫ hom) ≫ P.pullbackMap (𝟙 U) x =
            P.pullbackMap (𝟙 U) x ≫
              (hom ≫ P.pullbackMap (𝟙 U) x) := by simp [Category.assoc]
        _ = P.pullbackMap (𝟙 U) x ≫ 𝟙 x.1 := by rw [hom_fac]
        _ = P.pullbackMap (𝟙 U) x := by simp
        _ = (𝟙 _ : _ ⟶ _) ≫ P.pullbackMap (𝟙 U) x := by simp
  have component_fac (x : Functor.Fiber p U) :
      (component x).hom.1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
    have h := (component x).hom_inv_id
    change (component x).hom.1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 at h
    exact h
  have pullbackMap_fac {x y : Functor.Fiber p U} (φ : x ⟶ y) :
      ((P.pullbackFunctor (𝟙 U)).map φ).1 ≫ P.pullbackMap (𝟙 U) y =
        P.pullbackMap (𝟙 U) x ≫ φ.1 := by
    letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
    letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) y) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) y
    letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    have hφ' : p.IsHomLift (𝟙 U)
        (P.pullbackMap (𝟙 U) x ≫ φ.1) := by
      exact IsHomLift.comp_lift_id_right' p (𝟙 U)
        (P.pullbackMap (𝟙 U) x) U φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (𝟙 U)
        (P.pullbackMap (𝟙 U) y) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (P.pullbackMap (𝟙 U) x ≫ φ.1) hφ') ≫
          P.pullbackMap (𝟙 U) y = P.pullbackMap (𝟙 U) x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac p (𝟙 U)
      (P.pullbackMap (𝟙 U) y) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
      (P.pullbackMap (𝟙 U) x ≫ φ.1)
  let α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U) :=
    NatIso.ofComponents component (by
      intro x y φ
      apply Functor.Fiber.hom_ext
      change φ.1 ≫ (component y).hom.1 =
        (component x).hom.1 ≫ ((P.pullbackFunctor (𝟙 U)).map φ).1
      letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) y) :=
        P.pullbackMap_isStronglyCartesian (𝟙 U) y
      letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
      letI : p.IsHomLift (𝟙 U) (component x).hom.1 :=
        (component x).hom.2
      letI : p.IsHomLift (𝟙 U) (component y).hom.1 :=
        (component y).hom.2
      letI : p.IsHomLift (𝟙 U)
          (φ.1 ≫ (component y).hom.1) := by infer_instance
      letI : p.IsHomLift (𝟙 U)
          ((component x).hom.1 ≫ ((P.pullbackFunctor (𝟙 U)).map φ).1) := by
        infer_instance
      apply Functor.IsStronglyCartesian.ext p (𝟙 U)
        (P.pullbackMap (𝟙 U) y) (𝟙 U)
      calc
        (φ.1 ≫ (component y).hom.1) ≫ P.pullbackMap (𝟙 U) y =
            φ.1 ≫ ((component y).hom.1 ≫ P.pullbackMap (𝟙 U) y) := by
              simp [Category.assoc]
        _ = φ.1 := by
          rw [component_fac y]
          simp
        _ = (component x).hom.1 ≫
            (P.pullbackMap (𝟙 U) x ≫ φ.1) := by
              rw [component_fac x]
              simp
        _ = (component x).hom.1 ≫
            (((P.pullbackFunctor (𝟙 U)).map φ).1 ≫
              P.pullbackMap (𝟙 U) y) := by rw [pullbackMap_fac]
        _ = ((component x).hom.1 ≫
            ((P.pullbackFunctor (𝟙 U)).map φ).1) ≫
              P.pullbackMap (𝟙 U) y := by simp [Category.assoc])
  refine ⟨α, ?_, ?_⟩
  · intro x
    change (component x).hom.1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
    exact component_fac x
  · intro β hβ
    apply Iso.ext
    apply NatTrans.ext
    funext x
    apply Functor.Fiber.hom_ext
    change (β.hom.app x).1 = (α.hom.app x).1
    letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    letI : p.IsHomLift (𝟙 U) (β.hom.app x).1 := (β.hom.app x).2
    letI : p.IsHomLift (𝟙 U) (α.hom.app x).1 := (α.hom.app x).2
    apply Functor.IsStronglyCartesian.ext p (𝟙 U)
      (P.pullbackMap (𝟙 U) x) (𝟙 U)
    calc
      (β.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
        have hβx := hβ x
        change (β.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 at hβx
        exact hβx
      _ = (α.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x := by
        exact (component_fac x).symm

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
      (overNatIsoOfUnderlying
        (by
          simpa only [overFunctor, FibredCategoryOverHom.comp, CategoryOver.comp,
            CategoryOver.Hom.leftHom, Over.comp_left, Cat.Hom.comp_toFunctor] using
            Functor.associator (overFunctor F.underlying)
              (overFunctor G.underlying) (overFunctor H.underlying)))
  leftUnitor F :=
    fibredHomIsoOfUnderlying
      (overNatIsoOfUnderlying
        (Functor.leftUnitor (overFunctor F.underlying)))
  rightUnitor F :=
    fibredHomIsoOfUnderlying
      (overNatIsoOfUnderlying
        (Functor.rightUnitor (overFunctor F.underlying)))
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
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ }
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
  letI : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map φ) φ := hφ
  let αa := eFG'.hom.app a
  let αb := eFG'.hom.app b
  letI : IsIso αa := by
    change IsIso (eFG'.hom.app a)
    exact NatIso.hom_app_isIso eFG' a
  letI : IsIso αb := by
    change IsIso (eFG'.hom.app b)
    exact NatIso.hom_app_isIso eFG' b
  letI : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map αa) αa := by infer_instance
  letI : (structureFunctor X).IsStronglyCartesian
      ((structureFunctor X).map αb) αb := by infer_instance
  let αbinv := inv αb
  letI : IsIso αbinv := by
    dsimp [αbinv]
    infer_instance
  letI : (structureFunctor X).IsStronglyCartesian
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
  letI : (structureFunctor Y).IsHomLift
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
  letI : (structureFunctor X).IsHomLift
      (gX ≫ (structureFunctor X).map
        ((overFunctor G).map ((overFunctor F).map φ)))
      ((overFunctor G).map τ) := hGτ
  letI : (structureFunctor X).IsStronglyCartesian
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
  letI : (structureFunctor X).IsHomLift gX δ := hδ
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
        simp [εc, Category.assoc]
  refine ⟨χ, ⟨hχlift, hχfac⟩, ?_⟩
  intro χ' hχ'
  rcases hχ' with ⟨hχ'lift, hχ'fac⟩
  letI : (structureFunctor Y).IsHomLift g χ' := hχ'lift
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
        simp [Category.assoc]
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
    letI : (structureFunctor X).IsFibered := hX
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro y R f
    let hGy := congrArg (fun K : Y.left ⥤ C => K.obj y) (overFunctor_comm G)
    let fX := f ≫ eqToHom hGy.symm
    obtain ⟨x, φ, hφ⟩ :=
      hX.toIsPreFibered.exists_isCartesian' fX
    letI : (structureFunctor X).IsCartesian fX φ := hφ
    letI : (structureFunctor X).IsStronglyCartesian fX φ := inferInstance
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
    letI : (structureFunctor Y).IsStronglyCartesian
        ((structureFunctor Y).map ((overFunctor F).map φ)) ((overFunctor F).map φ) := hFφ
    let e := eGF'.hom.app y
    letI : IsIso e := by
      change IsIso (eGF'.hom.app y)
      exact NatIso.hom_app_isIso eGF' y
    letI : (structureFunctor Y).IsStronglyCartesian
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
    letI : (structureFunctor Y).IsHomLift f ψ := hψlift
    have hψstrong : (structureFunctor Y).IsStronglyCartesian f ψ := by
      let u := eqToHom hFGx.symm
      let q := (structureFunctor Y).map ((overFunctor F).map φ) ≫
        (structureFunctor Y).map e
      letI : (structureFunctor Y).IsStronglyCartesian q ψ := by
        simpa [q, ψ] using hcomp
      constructor
      intro c g τ hτ
      letI : (structureFunctor Y).IsHomLift (g ≫ f) τ := hτ
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
      letI : (structureFunctor Y).IsHomLift g χ' := hχ'base
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
    letI : (structureFunctor Y).IsFibered := hY
    refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
    intro x R f
    let hFx := congrArg (fun K : X.left ⥤ C => K.obj x) (overFunctor_comm F)
    let fY := f ≫ eqToHom hFx.symm
    obtain ⟨y, φ, hφ⟩ := hY.toIsPreFibered.exists_isCartesian' fY
    letI : (structureFunctor Y).IsCartesian fY φ := hφ
    letI : (structureFunctor Y).IsStronglyCartesian fY φ := inferInstance
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
    letI : (structureFunctor X).IsStronglyCartesian
        ((structureFunctor X).map ((overFunctor G).map φ)) ((overFunctor G).map φ) := hGφ
    let e := eFG'.hom.app x
    letI : IsIso e := by
      change IsIso (eFG'.hom.app x)
      exact NatIso.hom_app_isIso eFG' x
    letI : (structureFunctor X).IsStronglyCartesian
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
    letI : (structureFunctor X).IsHomLift f ψ := hψlift
    have hψstrong : (structureFunctor X).IsStronglyCartesian f ψ := by
      let u := eqToHom hGFy.symm
      let q := (structureFunctor X).map ((overFunctor G).map φ) ≫
        (structureFunctor X).map e
      letI : (structureFunctor X).IsStronglyCartesian q ψ := by
        simpa [q, ψ] using hcomp
      constructor
      intro c g τ hτ
      letI : (structureFunctor X).IsHomLift (g ≫ f) τ := hτ
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
      letI : (structureFunctor X).IsHomLift g χ' := hχ'base
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

structure FibredTwoFibreProduct {C : Cat.{v, u}}
    {X Y S : FibredCategoryOver C}
    (F : FibredCategoryOverHom X S) (G : FibredCategoryOverHom Y S) where
  diagram : TwoFibreProductOverDiagram F.underlying G.underlying
  apex_fibred : (diagram.base).IsFibered
  left_preserves : MapsStronglyCartesian diagram.base
    (structureFunctor X.underlying) diagram.left
  right_preserves : MapsStronglyCartesian diagram.base
    (structureFunctor Y.underlying) diagram.right
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
  letI : q.IsStronglyCartesian f.left ψ := hψ
  letI : q.IsHomLift f.left ψ := by infer_instance
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
  letI : p'.IsHomLift f ψ := by
    rw [hf]
    infer_instance
  have hψ' : p'.IsStronglyCartesian f ψ := by
    constructor
    intro z g τ hτ
    letI : p'.IsHomLift (g ≫ f) τ := hτ
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
    letI : (p' ⋙ Over.forget U).IsHomLift g.left χ := hχ
    have hχmap : g.left = (p'.map χ).left := by
      change g.left = (p' ⋙ Over.forget U).map χ
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _
        (p' ⋙ Over.forget U) z y g.left χ hχ
    have hg : g = p'.map χ := by
      apply Over.OverMorphism.ext
      exact hχmap
    letI : p'.IsHomLift g χ := by
      rw [hg]
      infer_instance
    refine ⟨χ, ⟨inferInstance, hχfac⟩, ?_⟩
    intro χ' hχ'
    rcases hχ' with ⟨hχ'base, hχ'fac⟩
    letI : p'.IsHomLift g χ' := hχ'base
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
  letI : p.IsStronglyCartesian ψ φ := hφ
  have hdomP : p.obj a' = b :=
    CategoryTheory.IsHomLift.domain_eq p ψ φ
  subst b
  have hψmap : ψ = p.map φ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift p ψ φ
  letI : q.IsStronglyCartesian f ψ := hψ
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
  letI : p.IsStronglyCartesian (p.map φ) φ := hφ'
  letI : q.IsStronglyCartesian (q.map (p.map φ)) (p.map φ) := hψ'
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
  letI : Functor.IsStronglyCartesian p
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

private theorem comma_property_base_isFibred
    {X Y C : Type*} [Category* X] [Category* Y] [Category* C]
    (q : Y ⥤ C) (H : X ⥤ Y)
    [q.IsFibered] [(H ⋙ q).IsFibered]
    (P : ObjectProperty (Comma (𝟭 Y) H))
    (hP : ∀ ξ : P.FullSubcategory, ∃ U : C,
      q.obj ξ.obj.left = U ∧
        q.obj (H.obj ξ.obj.right) = U ∧
          q.IsHomLift (𝟙 U) ξ.obj.hom)
    (preserves : ∀ {a b : X} (φ : a ⟶ b),
      Functor.IsStronglyCartesian (H ⋙ q) ((H ⋙ q).map φ) φ →
        Functor.IsStronglyCartesian q (q.map (H.map φ)) (H.map φ)) :
    (P.ι ⋙ Comma.fst (𝟭 Y) H ⋙ q).IsFibered := by
  classical
  let base : P.FullSubcategory ⥤ C := P.ι ⋙ Comma.fst (𝟭 Y) H ⋙ q
  let lifts : ∀ {A D : Type*} [Category* A] [Category* D]
      (r : A ⥤ D) [r.IsFibered] (a : A) (R : D)
      (f : R ⟶ r.obj a),
      ∃ (b : A) (φ : b ⟶ a), Functor.IsStronglyCartesian r f φ := by
    intro A D _ _ r _ a R f
    obtain ⟨b, φ, hφ⟩ :=
      (inferInstance : r.IsFibered).toIsPreFibered.exists_isCartesian' f
    exact ⟨b, φ, @Functor.IsFibered.isStronglyCartesian_of_isCartesian
      _ _ _ _ r inferInstance R _ f _ _ φ hφ⟩
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro ξ R f
  rcases hP ξ with ⟨U, hy, hx, hξ⟩
  change R ⟶ q.obj ξ.obj.left at f
  let hxy : (H ⋙ q).obj ξ.obj.right = q.obj ξ.obj.left := hx.trans hy.symm
  let fX := f ≫ eqToHom hxy.symm
  obtain ⟨x', φ, hφ⟩ := lifts (H ⋙ q) ξ.obj.right R fX
  letI : (H ⋙ q).IsStronglyCartesian fX φ := hφ
  have hdomX : (H ⋙ q).obj x' = R :=
    CategoryTheory.IsHomLift.domain_eq (H ⋙ q) fX φ
  subst R
  have hmapX : fX = (H ⋙ q).map φ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (H ⋙ q) fX φ
  obtain ⟨y', ψ, hψ⟩ := lifts q ξ.obj.left ((H ⋙ q).obj x') f
  letI : q.IsStronglyCartesian f ψ := hψ
  have hdomY : q.obj y' = (H ⋙ q).obj x' :=
    CategoryTheory.IsHomLift.domain_eq q f ψ
  have hmapY : q.map ψ = eqToHom hdomY ≫ f := by
    simpa [base, Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q f ψ)
  let hHx' : q.obj (H.obj x') = (H ⋙ q).obj x' := rfl
  let hHx : q.obj (H.obj ξ.obj.right) = (H ⋙ q).obj ξ.obj.right := rfl
  let hHy : q.obj (H.obj ξ.obj.right) = U := hHx.trans hx
  have hHmap : q.map (H.map φ) =
      eqToHom hHx' ≫ (H ⋙ q).map φ ≫ eqToHom hHx.symm := by
    simp [Functor.comp_map]
  have hξmap : q.map ξ.obj.hom =
      eqToHom hy ≫ (𝟙 U) ≫ eqToHom hHy.symm := by
    letI : q.IsHomLift (𝟙 U) ξ.obj.hom := hξ
    simpa [Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q (𝟙 U) ξ.obj.hom)
  let g : q.obj y' ⟶ q.obj (H.obj x') :=
    eqToHom hdomY ≫ eqToHom hHx'.symm
  have hφ' : (H ⋙ q).IsStronglyCartesian ((H ⋙ q).map φ) φ := by
    simpa [hmapX] using
      (inferInstance : (H ⋙ q).IsStronglyCartesian fX φ)
  letI : (H ⋙ q).IsStronglyCartesian ((H ⋙ q).map φ) φ := hφ'
  letI : q.IsStronglyCartesian (q.map (H.map φ)) (H.map φ) :=
    preserves φ hφ'
  have hfactor : q.map (ψ ≫ ξ.obj.hom) = g ≫ q.map (H.map φ) := by
    rw [Functor.map_comp, hmapY, hξmap, hHmap, ← hmapX]
    simp only [g, fX, hxy, hHx, hHx', hHy, Category.assoc,
      eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id]
  obtain ⟨χ, ⟨hχ, hχeq⟩, hχuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property q
      (q.map (H.map φ)) (H.map φ) g (q.map (ψ ≫ ξ.obj.hom)) hfactor
      (ψ ≫ ξ.obj.hom)
  have hχmap : g = q.map χ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift q g χ
  have hχbase : q.IsHomLift (𝟙 ((H ⋙ q).obj x')) χ := by
    apply CategoryTheory.IsHomLift.of_fac q (𝟙 ((H ⋙ q).obj x')) χ
      hdomY hHx'
    rw [← hχmap]
    simp [g, Category.assoc]
  let ξ' : P.FullSubcategory :=
    { obj := { left := y', right := x', hom := χ }
      property := ⟨(H ⋙ q).obj x', hdomY, rfl, hχbase⟩ }
  let h : ξ' ⟶ ξ := ObjectProperty.homMk
    { left := ψ, right := φ, w := hχeq.symm }
  refine ⟨ξ', h, ?_⟩
  have hbase : base.IsHomLift f h := by
    let hdomY' : base.obj ξ' = (H ⋙ q).obj x' := by
      change q.obj y' = (H ⋙ q).obj x'
      exact hdomY
    change q.obj y' = (H ⋙ q).obj x' at hdomY'
    have hcod : base.obj ξ = q.obj ξ.obj.left := by
      change q.obj ξ.obj.left = q.obj ξ.obj.left
      rfl
    apply CategoryTheory.IsHomLift.of_fac' base f h hdomY' hcod
    simp only [base, h, ξ', Functor.comp_map, ObjectProperty.ι_map,
      Comma.fst_map, ObjectProperty.homMk, hmapY, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
    change eqToHom hdomY ≫ f =
      eqToHom hdomY ≫ f ≫ eqToHom (rfl : q.obj ξ.obj.left = q.obj ξ.obj.left)
    simp
  refine { toIsHomLift := hbase, universal_property' := ?_ }
  intro ζ g₀ τ hτ
  rcases hP ζ with ⟨U₀, hy₀, hx₀, hζ⟩
  letI : base.IsHomLift (g₀ ≫ f) τ := hτ
  have hτmap : g₀ ≫ f = base.map τ :=
    CategoryTheory.IsHomLift.eq_of_isHomLift base (g₀ ≫ f) τ
  change q.obj ζ.obj.left ⟶ (H ⋙ q).obj x' at g₀
  have hτmap' : g₀ ≫ f = q.map τ.hom.left := by
    simpa [base] using hτmap
  have hτq : q.IsHomLift (g₀ ≫ f) τ.hom.left := by
    rw [hτmap']
    infer_instance
  obtain ⟨α, ⟨hα, hαeq⟩, hαuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property q f ψ
      g₀ (g₀ ≫ f) rfl τ.hom.left
  let hxy₀ : (H ⋙ q).obj ζ.obj.right = q.obj ζ.obj.left :=
    hx₀.trans hy₀.symm
  let gX : (H ⋙ q).obj ζ.obj.right ⟶ (H ⋙ q).obj x' :=
    eqToHom hxy₀ ≫ g₀ ≫ eqToHom hdomY.symm ≫ g
  have hζmap : q.map ζ.obj.hom =
      eqToHom hy₀ ≫ (𝟙 U₀) ≫ eqToHom hx₀.symm := by
    letI : q.IsHomLift (𝟙 U₀) ζ.obj.hom := hζ
    simpa [Category.assoc] using
      (CategoryTheory.IsHomLift.fac' q (𝟙 U₀) ζ.obj.hom)
  have hαmap : q.map α = g₀ ≫ eqToHom hdomY.symm := by
    have h := CategoryTheory.IsHomLift.fac' q g₀ α
    simpa [Category.assoc] using h
  have hτfactor : (H ⋙ q).map τ.hom.right =
      gX ≫ (H ⋙ q).map φ := by
    have hf : f = eqToHom hdomY.symm ≫ q.map ψ := by
      rw [hmapY]
      simp
    have hχcomp : q.map ψ ≫ q.map ξ.obj.hom =
        q.map χ ≫ q.map (H.map φ) := by
      rw [← q.map_comp, ← q.map_comp, hχeq]
    have hτw := congrArg q.map τ.hom.w
    change q.map (τ.hom.left ≫ ξ.obj.hom) =
      q.map (ζ.obj.hom ≫ H.map τ.hom.right) at hτw
    rw [q.map_comp, q.map_comp] at hτw
    rw [← hτmap'] at hτw
    have hτw' :
        g₀ ≫ eqToHom hdomY.symm ≫ q.map χ ≫ q.map (H.map φ) =
          q.map ζ.obj.hom ≫ q.map (H.map τ.hom.right) := by
      calc
        g₀ ≫ eqToHom hdomY.symm ≫ q.map χ ≫ q.map (H.map φ) =
            (g₀ ≫ f) ≫ q.map ξ.obj.hom := by
              rw [← hχcomp, hmapY]
              simp [Category.assoc]
        _ = q.map ζ.obj.hom ≫ q.map (H.map τ.hom.right) := hτw
    have hτw'' := congrArg
      (fun k => eqToHom hx₀ ≫ eqToHom hy₀.symm ≫ k) hτw'.symm
    simpa [hζmap, gX, hχmap, hxy₀, hx₀, hy₀, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]
      using hτw''
  have hτp : (H ⋙ q).IsHomLift
      (gX ≫ (H ⋙ q).map φ) τ.hom.right := by
    have hmap : (H ⋙ q).IsHomLift ((H ⋙ q).map τ.hom.right) τ.hom.right :=
      inferInstance
    rw [hτfactor] at hmap
    exact hmap
  letI : (H ⋙ q).IsHomLift
      (gX ≫ (H ⋙ q).map φ) τ.hom.right := hτp
  obtain ⟨β, ⟨hβ, hβeq⟩, hβuniq⟩ :=
    Functor.IsStronglyCartesian.universal_property (H ⋙ q)
      ((H ⋙ q).map φ) φ gX ((H ⋙ q).map τ.hom.right) hτfactor τ.hom.right
  have hβmap : gX = (H ⋙ q).map β :=
    CategoryTheory.IsHomLift.eq_of_isHomLift (H ⋙ q) gX β
  let gcomp : q.obj ζ.obj.left ⟶ q.obj (H.obj x') :=
    g₀ ≫ eqToHom hdomY.symm ≫ g
  have hα' : q.IsHomLift (g₀ ≫ eqToHom hdomY.symm) α := by
    apply CategoryTheory.IsHomLift.of_fac q
      (g₀ ≫ eqToHom hdomY.symm) α rfl rfl
    simpa using hαmap.symm
  have hother : q.IsHomLift gcomp
      (ζ.obj.hom ≫ H.map β) := by
    apply CategoryTheory.IsHomLift.of_fac' q gcomp
      (ζ.obj.hom ≫ H.map β) rfl rfl
    have hβmap' : q.map (H.map β) = gX := by
      simpa [Functor.comp_map] using hβmap.symm
    have hqζ : q.map ζ.obj.hom ≫ gX = gcomp := by
      rw [hζmap]
      simp [gX, gcomp, hxy₀, hx₀, hy₀, Category.assoc]
    simp [Functor.map_comp, hβmap', hqζ, Category.assoc]
  letI : q.IsHomLift (g₀ ≫ eqToHom hdomY.symm) α := hα'
  letI : q.IsHomLift gcomp (α ≫ χ) := by infer_instance
  letI : q.IsHomLift gcomp (ζ.obj.hom ≫ H.map β) := hother
  have hcomp : (α ≫ χ) ≫ H.map φ =
      (ζ.obj.hom ≫ H.map β) ≫ H.map φ := by
    have hτw : τ.hom.left ≫ ξ.obj.hom =
        ζ.obj.hom ≫ H.map τ.hom.right := by
      simpa only [Functor.id_map] using τ.hom.w
    calc
      (α ≫ χ) ≫ H.map φ = α ≫ (χ ≫ H.map φ) := by simp [Category.assoc]
      _ = α ≫ (ψ ≫ ξ.obj.hom) := by rw [hχeq]
      _ = (α ≫ ψ) ≫ ξ.obj.hom := by simp [Category.assoc]
      _ = τ.hom.left ≫ ξ.obj.hom := by rw [hαeq]
      _ = (ζ.obj.hom ≫ H.map β) ≫ H.map φ := by
        rw [hτw, ← hβeq, Functor.map_comp]
        simp [Category.assoc]
  have hw : α ≫ χ = ζ.obj.hom ≫ H.map β :=
    Functor.IsStronglyCartesian.ext q (q.map (H.map φ)) (H.map φ)
      gcomp hcomp
  let δ : ζ ⟶ ξ' := ObjectProperty.homMk
    { left := α, right := β, w := hw }
  have hδbase : base.IsHomLift g₀ δ := by
    apply CategoryTheory.IsHomLift.of_fac' base g₀ δ rfl hdomY
    change q.map α = eqToHom (rfl : q.obj ζ.obj.left = q.obj ζ.obj.left) ≫
      g₀ ≫ eqToHom hdomY.symm
    rw [hαmap]
    simp
  refine ⟨δ, ⟨hδbase, ?_⟩, ?_⟩
  · apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · exact hαeq
    · exact hβeq
  intro δ' hδ'
  rcases hδ' with ⟨hδ'base, hδ'eq⟩
  letI : base.IsHomLift g₀ δ' := hδ'base
  have hδ'leftmap : q.map δ'.hom.left =
      g₀ ≫ eqToHom hdomY.symm := by
    have h := CategoryTheory.IsHomLift.fac' base g₀ δ'
    have hdom' : base.obj ζ = q.obj ζ.obj.left := rfl
    have hdom'' : hdom' =
        (rfl : q.obj ζ.obj.left = q.obj ζ.obj.left) := Subsingleton.elim _ _
    have hdom : CategoryTheory.IsHomLift.domain_eq base g₀ δ' =
        hdom' := Subsingleton.elim _ _
    have hcod' : base.obj ξ' = (H ⋙ q).obj x' := hdomY
    have hcod'' : hcod' = hdomY := Subsingleton.elim _ _
    have hcod : CategoryTheory.IsHomLift.codomain_eq base g₀ δ' =
        hcod' := Subsingleton.elim _ _
    rw [hdom, hcod, hdom'', hcod''] at h
    simpa only [base, Functor.comp_map, ObjectProperty.ι_map,
      Comma.fst_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id, Category.assoc] using h
  have hδ'left : q.IsHomLift g₀ δ'.hom.left := by
    apply CategoryTheory.IsHomLift.of_fac' q g₀ δ'.hom.left rfl hdomY
    simpa using hδ'leftmap
  have hδ'eq' := congrArg (fun k => k.hom) hδ'eq
  have hδ'left_eq : δ'.hom.left ≫ h.hom.left = τ.hom.left := by
    exact congrArg CommaMorphism.left hδ'eq'
  have hδ'right_eq : δ'.hom.right ≫ h.hom.right = τ.hom.right := by
    exact congrArg CommaMorphism.right hδ'eq'
  apply ObjectProperty.hom_ext
  apply CommaMorphism.ext
  · apply hαuniq
    exact ⟨hδ'left, by simpa [h] using hδ'left_eq⟩
  · apply hβuniq
    have hδ'rightmap : gX = (H ⋙ q).map δ'.hom.right := by
      have hδ'w := congrArg q.map δ'.hom.w
      have hδ'w' : q.map δ'.hom.left ≫ q.map ξ'.obj.hom =
          q.map ζ.obj.hom ≫ q.map (H.map δ'.hom.right) := by
        simpa only [Functor.map_comp, Functor.id_map] using hδ'w
      rw [Functor.comp_map]
      have h := congrArg
        (fun k => eqToHom hx₀ ≫ eqToHom hy₀.symm ≫ k) hδ'w'
      rw [hδ'leftmap, ← hχmap, hζmap] at h
      simpa [gX, g, hxy₀, Category.assoc, eqToHom_trans,
        eqToHom_refl, Category.id_comp, Category.comp_id] using h
    have hδ'right : (H ⋙ q).IsHomLift gX δ'.hom.right := by
      have hmap : (H ⋙ q).IsHomLift ((H ⋙ q).map δ'.hom.right)
          δ'.hom.right := inferInstance
      rw [← hδ'rightmap] at hmap
      exact hmap
    exact ⟨hδ'right, by simpa [h] using hδ'right_eq⟩

theorem ameliorationBase_isFibred {C : Cat.{v, u}}
    {X Y : FibredCategoryOver C} (F : FibredCategoryOverHom X Y) :
    (ameliorationBase F).IsFibered := by
  letI : (overFunctor F.underlying ⋙ structureFunctor Y.underlying).IsFibered := by
    rw [overFunctor_comm F.underlying]
    infer_instance
  change ((ameliorationProperty F).ι ⋙
      Comma.fst (𝟭 Y.underlying.left) (overFunctor F.underlying) ⋙
      structureFunctor Y.underlying).IsFibered
  apply comma_property_base_isFibred
    (q := structureFunctor Y.underlying)
    (H := overFunctor F.underlying)
    (P := ameliorationProperty F)
  · intro ξ
    exact ξ.property
  · intro a b φ hφ
    apply F.preserves φ
    simpa only [← overFunctor_comm F.underlying] using hφ

/- The three projections and their comparison maps are packaged as a theorem
   interface.  The final field records the source's necessary correction: the
   functor `v : X' ⥤ Y` is itself a fibred functor over `Y`. -/
structure AmeliorationFactorization
    {C : Cat.{v, u}} {X Y : FibredCategoryOver C}
    (F : FibredCategoryOverHom X Y) where
  middle : FibredCategoryOver C
  u : FibredCategoryOverHom X middle
  v : FibredCategoryOverHom middle Y
  w : FibredCategoryOverHom middle X
  factorization : F = FibredCategoryOverHom.comp u v
  u_fully_faithful : Nonempty (overFunctor u.underlying).FullyFaithful
  w_left_adjoint_u : Nonempty (overFunctor w.underlying ⊣ overFunctor u.underlying)
  v_fibred_over_Y : (overFunctor v.underlying).IsFibered

theorem ameliorate_fibred_morphism
    {C : Cat.{v, u}} (X Y : FibredCategoryOver C)
    (F : FibredCategoryOverHom X Y) :
    Nonempty (AmeliorationFactorization F) := by
  sorry

end

end Formalization.Books.Categories.Unit33
