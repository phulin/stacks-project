import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fiber

namespace IdentityScratch

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

structure TestPullbackChoice
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] where
  pullback : ∀ {R S : C} (_f : R ⟶ S) (_x : Functor.Fiber p S),
    Functor.Fiber p R
  pullbackMap : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
    (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ X).obj
        (pullback f x) ⟶ x.1
  pullbackMap_isStronglyCartesian : ∀ {R S : C} (f : R ⟶ S)
    (x : Functor.Fiber p S),
    Functor.IsStronglyCartesian p f (pullbackMap f x)

attribute [instance] TestPullbackChoice.pullbackMap_isStronglyCartesian

namespace TestPullbackChoice

variable {X C : Type*} [Category* X] [Category* C]
variable {p : X ⥤ C} [p.IsFibered]

def pullbackFunctor (P : TestPullbackChoice p) {R S : C} (f : R ⟶ S) :
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

end TestPullbackChoice

theorem iso_is_stronglyCartesian
    {X C : Type*} [Category* X] [Category* C] (p : X ⥤ C)
    {R S : C} {a b : X} (f : R ⟶ S) (e : a ≅ b)
    [p.IsHomLift f e.hom] :
    Functor.IsStronglyCartesian p f e.hom := by
  infer_instance

theorem test_identity_iso
    {X C : Type*} [Category* X] [Category* C]
    (p : X ⥤ C) [p.IsFibered] (P : TestPullbackChoice p) (U : C) :
    ∃! α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U),
      ∀ x : Functor.Fiber p U,
        Functor.Fiber.fiberInclusion.map (α.hom.app x) ≫
            P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
  classical
  let component : ∀ x : Functor.Fiber p U,
      x ≅ P.pullback (𝟙 U) x := by
    intro x
    letI : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    letI : p.IsStronglyCartesian (𝟙 U) (𝟙 x.1) := by infer_instance
    letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      P.pullbackMap_isStronglyCartesian (𝟙 U) x
    let hom : x.1 ⟶
        (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ X).obj
          (P.pullback (𝟙 U) x) :=
      @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (𝟙 U)
        (P.pullbackMap (𝟙 U) x) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (𝟙 x.1) (by infer_instance)
    have hom_lift : p.IsHomLift (𝟙 U) hom := by
      dsimp [hom]
      exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _
        (𝟙 U) (P.pullbackMap (𝟙 U) x) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (𝟙 x.1) (by infer_instance)
    letI : p.IsHomLift (𝟙 U) hom := hom_lift
    letI : p.IsHomLift (𝟙 U) (P.pullbackMap (𝟙 U) x) :=
      (P.pullbackMap_isStronglyCartesian (𝟙 U) x).toIsHomLift
    have hom_fac : hom ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
      dsimp [hom]
      exact Functor.IsStronglyCartesian.fac p (𝟙 U)
        (P.pullbackMap (𝟙 U) x) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
        (𝟙 x.1)
    let homF : x ⟶ P.pullback (𝟙 U) x := ⟨hom, hom_lift⟩
    let invF : P.pullback (𝟙 U) x ⟶ x :=
      ⟨P.pullbackMap (𝟙 U) x,
        (P.pullbackMap_isStronglyCartesian (𝟙 U) x).toIsHomLift⟩
    refine { hom := homF, inv := invF, hom_inv_id := ?_, inv_hom_id := ?_ }
    · apply Functor.Fiber.hom_ext
      change hom ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
      exact hom_fac
    · apply Functor.Fiber.hom_ext
      change P.pullbackMap (𝟙 U) x ≫ hom = 𝟙 _
      letI : p.IsHomLift (𝟙 U)
          (P.pullbackMap (𝟙 U) x ≫ hom) :=
        by
          simpa using IsHomLift.comp p (𝟙 U) (𝟙 U)
            (P.pullbackMap (𝟙 U) x) hom
      letI : p.IsHomLift (𝟙 U)
          (𝟙 ((P.pullback (𝟙 U) x).1)) :=
        IsHomLift.id (P.pullback (𝟙 U) x).2
      have hEq :
          (P.pullbackMap (𝟙 U) x ≫ hom) ≫ P.pullbackMap (𝟙 U) x =
            (𝟙 ((P.pullback (𝟙 U) x).1)) ≫ P.pullbackMap (𝟙 U) x := by
        calc
          (P.pullbackMap (𝟙 U) x ≫ hom) ≫ P.pullbackMap (𝟙 U) x =
              P.pullbackMap (𝟙 U) x ≫
                (hom ≫ P.pullbackMap (𝟙 U) x) := by simp [Category.assoc]
          _ = P.pullbackMap (𝟙 U) x ≫ 𝟙 x.1 := by rw [hom_fac]
          _ = P.pullbackMap (𝟙 U) x := by simp
          _ = (𝟙 _ : _ ⟶ _) ≫ P.pullbackMap (𝟙 U) x := by simp
      exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
        (𝟙 U) (P.pullbackMap (𝟙 U) x)
        (P.pullbackMap_isStronglyCartesian (𝟙 U) x)
        _ _ (𝟙 U)
        (P.pullbackMap (𝟙 U) x ≫ hom) (𝟙 ((P.pullback (𝟙 U) x).1))
        (by
          simpa using IsHomLift.comp p (𝟙 U) (𝟙 U)
            (P.pullbackMap (𝟙 U) x) hom)
        (IsHomLift.id (P.pullback (𝟙 U) x).2) hEq
  have component_fac (x : Functor.Fiber p U) :
      Functor.Fiber.fiberInclusion.map ((component x).hom) ≫
          P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
    letI : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    change
      (Functor.IsStronglyCartesian.map p (𝟙 U)
          (P.pullbackMap (𝟙 U) x) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
          (𝟙 x.1)) ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1
    exact Functor.IsStronglyCartesian.fac p (𝟙 U)
      (P.pullbackMap (𝟙 U) x) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
      (𝟙 x.1)
  have pullbackMap_fac {x y : Functor.Fiber p U} (φ : x ⟶ y) :
      Functor.Fiber.fiberInclusion.map ((P.pullbackFunctor (𝟙 U)).map φ) ≫
          P.pullbackMap (𝟙 U) y =
        P.pullbackMap (𝟙 U) x ≫ Functor.Fiber.fiberInclusion.map φ := by
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
          P.pullbackMap (𝟙 U) y = P.pullbackMap (𝟙 U) x ≫
            φ.1
    exact Functor.IsStronglyCartesian.fac p (𝟙 U)
      (P.pullbackMap (𝟙 U) y) (f' := 𝟙 U) (g := 𝟙 U) (by simp)
      (P.pullbackMap (𝟙 U) x ≫ φ.1)
  let α : 𝟭 (Functor.Fiber p U) ≅ P.pullbackFunctor (𝟙 U) :=
    NatIso.ofComponents component (by
      intro x y φ
      apply Functor.Fiber.hom_ext
      change Functor.Fiber.fiberInclusion.map φ ≫
          Functor.Fiber.fiberInclusion.map ((component y).hom) =
        Functor.Fiber.fiberInclusion.map ((component x).hom) ≫
          Functor.Fiber.fiberInclusion.map ((P.pullbackFunctor (𝟙 U)).map φ)
      letI : p.IsStronglyCartesian (𝟙 U) (P.pullbackMap (𝟙 U) y) :=
        P.pullbackMap_isStronglyCartesian (𝟙 U) y
      have hφlift : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map φ) := by
        change p.IsHomLift (𝟙 U) φ.1
        exact φ.2
      letI : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map φ) := hφlift
      letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
      have hxLift : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component x).hom)) := by
        change p.IsHomLift (𝟙 U) (component x).hom.1
        exact (component x).hom.2
      letI : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component x).hom)) := hxLift
      letI : p.IsHomLift (𝟙 U) (component x).hom.1 := (component x).hom.2
      have hyLift : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component y).hom)) := by
        change p.IsHomLift (𝟙 U) (component y).hom.1
        exact (component y).hom.2
      letI : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component y).hom)) := hyLift
      letI : p.IsHomLift (𝟙 U) (component y).hom.1 := (component y).hom.2
      letI : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map φ ≫
            Functor.Fiber.fiberInclusion.map ((component y).hom)) := by
        simpa only [Category.id_comp] using
          IsHomLift.comp p (𝟙 U) (𝟙 U)
            (Functor.Fiber.fiberInclusion.map φ)
            (Functor.Fiber.fiberInclusion.map ((component y).hom))
      have hφ' : p.IsHomLift (𝟙 U)
          (P.pullbackMap (𝟙 U) x ≫ φ.1) :=
        IsHomLift.comp_lift_id_right' p (𝟙 U)
          (P.pullbackMap (𝟙 U) x) U φ.1
      let m := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ (𝟙 U)
        (P.pullbackMap (𝟙 U) y) _ _ _ (𝟙 U) (𝟙 U) (by simp)
        (P.pullbackMap (𝟙 U) x ≫ φ.1) hφ'
      have hm : p.IsHomLift (𝟙 U) m := by
        dsimp [m]
        exact @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ p _ _ _ _
          (𝟙 U) (P.pullbackMap (𝟙 U) y) _ _ _ (𝟙 U) (𝟙 U) (by simp)
          (P.pullbackMap (𝟙 U) x ≫ φ.1) hφ'
      letI : p.IsHomLift (𝟙 U) m := hm
      have hcomp : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component x).hom) ≫ m) := by
        simpa only [Category.id_comp] using
          IsHomLift.comp p (𝟙 U) (𝟙 U)
            (Functor.Fiber.fiberInclusion.map ((component x).hom)) m
      letI : p.IsHomLift (𝟙 U)
          (Functor.Fiber.fiberInclusion.map ((component x).hom) ≫ m) := hcomp
      change Functor.Fiber.fiberInclusion.map φ ≫
          Functor.Fiber.fiberInclusion.map ((component y).hom) =
        Functor.Fiber.fiberInclusion.map ((component x).hom) ≫ m
      refine Functor.IsStronglyCartesian.ext p (𝟙 U)
        (P.pullbackMap (𝟙 U) y) (𝟙 U) ?_
      change (φ.1 ≫ (component y).hom.1) ≫ P.pullbackMap (𝟙 U) y =
        ((component x).hom.1 ≫ m) ≫ P.pullbackMap (𝟙 U) y
      have hfac_y :
          (component y).hom.1 ≫ P.pullbackMap (𝟙 U) y =
            𝟙 y.1 := by
        exact component_fac y
      have hfac_x :
          (component x).hom.1 ≫ P.pullbackMap (𝟙 U) x =
            𝟙 x.1 := by
        exact component_fac x
      have hpullbackMap_fac := pullbackMap_fac φ
      change m ≫ P.pullbackMap (𝟙 U) y = P.pullbackMap (𝟙 U) x ≫ φ.1 at hpullbackMap_fac
      rw [Category.assoc, hfac_y]
      rw [Category.comp_id]
      rw [Category.assoc, hpullbackMap_fac]
      rw [← Category.assoc, hfac_x, Category.id_comp]
  refine ⟨α, ?_, ?_⟩
  · intro x
    change Functor.Fiber.fiberInclusion.map ((component x).hom) ≫
      P.pullbackMap (𝟙 U) x = 𝟙 x.1
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
    letI : p.IsHomLift (𝟙 U)
        (Functor.Fiber.fiberInclusion.map (β.hom.app x)) := by
      change p.IsHomLift (𝟙 U) (β.hom.app x).1
      exact (β.hom.app x).2
    letI : p.IsHomLift (𝟙 U)
        (Functor.Fiber.fiberInclusion.map (α.hom.app x)) := by
      change p.IsHomLift (𝟙 U) (α.hom.app x).1
      exact (α.hom.app x).2
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 U) (P.pullbackMap (𝟙 U) x)
      (P.pullbackMap_isStronglyCartesian (𝟙 U) x)
      _ _ (𝟙 U)
      (β.hom.app x).1 (α.hom.app x).1
      (β.hom.app x).2 (α.hom.app x).2 (by
        calc
          (β.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 := by
            have hβx := hβ x
            change (β.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 at hβx
            exact hβx
          _ = (α.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x := by
            have hcomponent_fac_x := component_fac x
            change (α.hom.app x).1 ≫ P.pullbackMap (𝟙 U) x = 𝟙 x.1 at hcomponent_fac_x
            exact hcomponent_fac_x.symm)

end

end IdentityScratch
