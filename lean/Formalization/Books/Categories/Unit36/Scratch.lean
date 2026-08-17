import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

namespace Scratch

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

structure PullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] where
  pullback : ∀ {R T : C} (_f : R ⟶ T) (_x : Functor.Fiber p T),
    Functor.Fiber p R
  pullbackMap : ∀ {R T : C} (f : R ⟶ T) (x : Functor.Fiber p T),
    (Functor.Fiber.fiberInclusion : Functor.Fiber p R ⥤ S).obj (pullback f x) ⟶ x.1
  pullbackMap_isStronglyCartesian : ∀ {R T : C} (f : R ⟶ T)
    (x : Functor.Fiber p T),
    Functor.IsStronglyCartesian p f (pullbackMap f x)

attribute [instance] PullbackChoice.pullbackMap_isStronglyCartesian

structure Obj
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  V : C
  U : C
  f : V ⟶ U
  x : Functor.Fiber p U

def reindex
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W : C} (A : Obj p P) (g : W ⟶ A.V) : Obj p P where
  V := W
  U := A.U
  f := g ≫ A.f
  x := A.x

example
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W V : C} (h : W ⟶ V) (A : Obj p P)
    (g : V ⟶ A.V) :
    reindex (reindex A g) h = reindex A (h ≫ g) := by
  cases A
  simp [reindex, Category.assoc]

def pullback
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : Obj p P) : Functor.Fiber p A.V :=
  P.pullback A.f A.x

structure Hom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {A B : Obj p P} where
  hom : (pullback A).1 ⟶ (pullback B).1

namespace Hom

@[ext]
lemma ext
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : Obj p P} {f g : Hom (A := A) (B := B) P}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Hom

namespace Hom

def base
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : Obj p P}
    (f : Hom (A := A) (B := B) P) : A.V ⟶ B.V :=
  eqToHom (pullback A).2.symm ≫
    p.map f.hom ≫ eqToHom (pullback B).2

end Hom

abbrev Cat
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) := Obj p P

instance cat
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) : Category (Cat p P) where
  Hom A B := Hom (A := A) (B := B) P
  id A := { hom := 𝟙 (pullback A).1 }
  comp f g := { hom := f.hom ≫ g.hom }
  id_comp f := by
    apply Hom.ext
    simp
  comp_id f := by
    apply Hom.ext
    simp
  assoc f g h := by
    apply Hom.ext
    simp [Category.assoc]

def projection
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    Cat p P ⥤ C where
  obj A := A.V
  map f := Hom.base f
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

theorem projection_isFibered
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    (projection P).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro B R f
  let A := reindex B f
  let hBStrong : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) :=
    P.pullbackMap_isStronglyCartesian B.f B.x
  letI : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) := hBStrong
  letI : p.IsStronglyCartesian (f ≫ B.f)
      (P.pullbackMap (f ≫ B.f) B.x) :=
    P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
  letI : p.IsHomLift (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x) := by
    exact @Functor.IsStronglyCartesian.toIsHomLift _ _ _ _ p _ _ _ _
      (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x)
  let φ : (pullback A).1 ⟶ (pullback B).1 :=
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
  letI : p.IsHomLift f φ := hφlift
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
    letI : p.IsStronglyCartesian (f ≫ B.f)
        (φ ≫ P.pullbackMap B.f B.x) := hcompStrong
    exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _ f B.f φ
      (P.pullbackMap B.f B.x) hBStrong hcompStrong hφlift
  let κ : A ⟶ B := { hom := φ }
  have hκbase : (projection P).map κ = f := by
    change eqToHom _ ≫ p.map φ ≫ eqToHom _ = f
    exact (CategoryTheory.IsHomLift.fac p f φ).symm
  have hκlift : (projection P).IsHomLift f κ := by
    have h := (inferInstance :
      (projection P).IsHomLift ((projection P).map κ) κ)
    rw [hκbase] at h
    exact h
  letI : (projection P).IsHomLift f κ := hκlift
  have hκstrong : (projection P).IsStronglyCartesian f κ := by
    letI : p.IsStronglyCartesian f φ := hφstrong
    constructor
    intro X g τ hτ
    let eX := (pullback X).2
    let eA := (pullback A).2
    let eB := (pullback B).2
    have hτmap : g ≫ f = (projection P).map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift (projection P) (g ≫ f) τ
    have hτmap' : g ≫ f =
        eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB := by
      simpa [projection, Hom.base] using hτmap
    let g₀ : p.obj (pullback X).1 ⟶ R := eqToHom eX ≫ g
    have hτp : p.IsHomLift (g₀ ≫ f) τ.hom := by
      apply CategoryTheory.IsHomLift.of_fac p (g₀ ≫ f) τ.hom rfl eB
      have h := congrArg (fun k => eqToHom eX ≫ k) hτmap'
      dsimp [g₀]
      simpa [Category.assoc] using h
    obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
      Functor.IsStronglyCartesian.universal_property p f φ
        g₀ (g₀ ≫ f) rfl τ.hom
    let χ' : X ⟶ A := { hom := χ }
    have hχfac' : g₀ = p.map χ ≫ eqToHom eA := by
      have hEq : CategoryTheory.IsHomLift.codomain_eq p g₀ χ = eA := by
        apply Subsingleton.elim
      rw [CategoryTheory.IsHomLift.fac p g₀ χ, hEq]
      simp
    have hχbase : (projection P).map χ' = g := by
      change eqToHom eX.symm ≫ p.map χ ≫ eqToHom eA = g
      rw [← hχfac']
      dsimp [g₀]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, id_comp]
    have hχ'lift : (projection P).IsHomLift g χ' := by
      have h := (inferInstance :
        (projection P).IsHomLift ((projection P).map χ') χ')
      rw [hχbase] at h
      exact h
    letI : (projection P).IsHomLift g χ' := hχ'lift
    have hχcomp : χ' ≫ κ = τ := by
      apply Hom.ext
      exact hχfac
    refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
    intro χ'' hχ''
    haveI : (projection P).IsHomLift g χ'' := hχ''.1
    have hχ''map : g = (projection P).map χ'' := by
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift C (Cat p P) _ _
        (projection P) X A g χ'' hχ''.1
    have hχ''p : p.IsHomLift g₀ χ''.hom := by
      apply CategoryTheory.IsHomLift.of_fac p g₀ χ''.hom rfl eA
      have h := congrArg (fun k => eqToHom eX ≫ k) hχ''map
      simpa [g₀, eX, eA, projection, Hom.base, Category.assoc] using h
    have hχ''comp : χ''.hom ≫ φ = τ.hom := by
      have hcomp := congrArg (fun h : X ⟶ B => h.hom) hχ''.2
      dsimp [κ] at hcomp
      exact hcomp
    have hhom : χ''.hom = χ :=
      hχuniq χ''.hom ⟨hχ''p, hχ''comp⟩
    exact Hom.ext hhom
  exact ⟨A, κ, hκstrong⟩

def IsOverNaturalIso {A C : Type*}
    [Category* A] [Category* C]
    (p : A ⥤ C) {F G : A ⥤ A}
    (h : F ⋙ p = G ⋙ p) (e : F ≅ G) : Prop :=
  ∀ x, p.map (e.hom.app x) =
    eqToHom (congrArg (fun H : A ⥤ C => H.obj x) h)

def IsEquivalentOverBase {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (p : A ⥤ C) (q : B ⥤ C) : Prop :=
  ∃ (F : A ⥤ B) (G : B ⥤ A),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      (∃ (e : F ⋙ G ≅ 𝟭 A)
        (h : (F ⋙ G) ⋙ p = (𝟭 A) ⋙ p),
        IsOverNaturalIso p h e) ∧
      (∃ (e : G ⋙ F ≅ 𝟭 B)
        (h : (G ⋙ F) ⋙ q = (𝟭 B) ⋙ q),
        IsOverNaturalIso q h e)

example {A C : Type*} [Category* A] [Category* C]
    (p : A ⥤ C) : IsEquivalentOverBase p p := by
  refine ⟨𝟭 _, 𝟭 _, rfl, rfl, ?_, ?_⟩
  · exact ⟨Iso.refl _, rfl, by intro x; simp⟩
  · exact ⟨Iso.refl _, rfl, by intro x; simp⟩

end
end Scratch
