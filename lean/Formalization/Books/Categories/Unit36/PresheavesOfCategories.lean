import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Categories, Chapter 36: Presheaves of categories

The source compares fibred categories with contravariant functors to `Cat`.
Mathlib's `Pseudofunctor.CoGrothendieck` is the canonical implementation of
the displayed construction, so the source-facing names below are thin bridges
to that construction.  The strictification category used in the proof of the
last lemma is also recorded explicitly.
-/

namespace Formalization.Books.Categories.Unit36

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Functor
open Opposite
open Formalization.Books.Categories.Unit29
open Formalization.Books.Categories.Unit33

universe vC uC vS uS vF uF vD uD

noncomputable section

/-! ## The presheaf-to-fibred-category construction -/

/-- Regard an ordinary functor into `Cat` as the pseudofunctor used by the
CoGrothendieck construction. -/
abbrev splitFibredPseudofunctor
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    PseudofunctorFromCategory Cᵒᵖ (Cat.{vS, uS}) :=
  ordinaryFunctorToPseudofunctor F

/-- The category `\mathcal S_F` associated to a presheaf of categories. -/
abbrev splitFibredCategory
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :=
  Pseudofunctor.CoGrothendieck (splitFibredPseudofunctor F)

/-- The projection `p_F : \mathcal S_F \to \mathcal C`. -/
abbrev splitFibredProjection
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    splitFibredCategory F ⥤ C :=
  Pseudofunctor.CoGrothendieck.forget (splitFibredPseudofunctor F)

/-- The restriction functor `f^*` attached to a base arrow
`f : V ⟶ U`. -/
abbrev splitRestriction
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U) :
    F.obj (Opposite.op U) ⥤ F.obj (Opposite.op V) :=
  (F.map f.op).toFunctor

theorem splitRestriction_comp
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    splitRestriction F (g ≫ f) =
      splitRestriction F f ⋙ splitRestriction F g := by
  change (F.map (g ≫ f).op).toFunctor =
    (F.map f.op).toFunctor ⋙ (F.map g.op).toFunctor
  rw [op_comp, F.map_comp]
  rfl

/-- The source's object description is the canonical CoGrothendieck object.
Its fields are the base object `U` and the fibre object `x`. -/
abbrev splitFibredObject
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :=
  splitFibredCategory F

/-- The source's morphism description is the canonical CoGrothendieck hom.
Its fields are the base arrow and the arrow in the source fibre. -/
abbrev splitFibredHom
    {C : Type uC} [Category.{vC} C]
  (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y : splitFibredCategory F} :=
  Pseudofunctor.CoGrothendieck.Hom
    (F := splitFibredPseudofunctor F) X Y

@[simp]
theorem splitFibredProjection_obj
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) (X : splitFibredCategory F) :
    (splitFibredProjection F).obj X = X.base :=
  rfl

@[simp]
theorem splitFibredProjection_map
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y : splitFibredCategory F} (f : X ⟶ Y) :
    (splitFibredProjection F).map f = f.base :=
  rfl

@[simp]
theorem splitFibred_id_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) (X : splitFibredCategory F) :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base :=
  rfl

@[simp]
theorem splitFibred_comp_base
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y Z : splitFibredCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

/- The fibre component of composition is the source's rule: pull back the
   second fibre arrow along the first base arrow, compose with the first
   fibre arrow, and use the canonical comparison supplied by the ordinary
   functor's composition law. -/
theorem splitFibred_comp_fiber
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {X Y Z : splitFibredCategory F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber =
      f.fiber ≫
        ((splitFibredPseudofunctor F).map f.base.op.toLoc).toFunctor.map g.fiber ≫
        ((splitFibredPseudofunctor F).mapComp
            g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber :=
  rfl

theorem splitFibredProjection_isFibered
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    (splitFibredProjection F).IsFibered := by
  infer_instance

/-- The canonical lift of `f : V ⟶ U` with codomain `(U, x)` is
`(f, id_{f^*x})`. -/
abbrev splitFibredCartesianDomain
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C}
    (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    splitFibredCategory F :=
  Pseudofunctor.CoGrothendieck.domainCartesianLift x f

abbrev splitFibredCartesianLift
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C}
    (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    splitFibredCartesianDomain F f x ⟶
      (⟨U, x⟩ : splitFibredCategory F) :=
  Pseudofunctor.CoGrothendieck.cartesianLift x f

theorem splitFibredCartesianLift_isHomLift
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    (splitFibredProjection F).IsHomLift f
      (splitFibredCartesianLift F f x) := by
  infer_instance

theorem splitFibredCartesianLift_isStronglyCartesian
    {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS})
    {V U : C} (f : V ⟶ U)
    (x : (splitFibredPseudofunctor F).obj ⟨Opposite.op U⟩) :
    Functor.IsStronglyCartesian (splitFibredProjection F) f
      (splitFibredCartesianLift F f x) := by
  exact Pseudofunctor.CoGrothendieck.isStronglyCartesian_homCartesianLift
    (F := splitFibredPseudofunctor F) x f

/-! ## Split fibred categories -/

/-- The source's ``isomorphic over `C`'' relation.  The strict inverse
functors are important here: the source distinguishes a split fibred category
from one which is merely equivalent to a split one. -/
def IsomorphicOverBase
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) : Prop :=
  ∃ (F : S ⥤ T) (G : T ⥤ S),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      F ⋙ G = 𝟭 S ∧ G ⋙ F = 𝟭 T

/-- The source's notion of being split, expressed as isomorphism over the
base category. -/
def IsSplitFibredCategory
    {C : Type uC} [Category.{vC} C]
  {S : Type uS} [Category.{vS} S]
    (p : S ⥤ C) : Prop :=
  p.IsFibered ∧
    ∃ F : Cᵒᵖ ⥤ Cat.{vF, uF},
      IsomorphicOverBase p (splitFibredProjection F)

theorem splitFibredCategory_isSplit
  {C : Type uC} [Category.{vC} C]
    (F : Cᵒᵖ ⥤ Cat.{vS, uS}) :
    IsSplitFibredCategory.{vC, uC, _, _, vS, uS}
      (splitFibredProjection F) := by
  constructor
  · exact splitFibredProjection_isFibered F
  · refine ⟨F, ?_⟩
    exact ⟨𝟭 _, 𝟭 _, Functor.id_comp _, Functor.id_comp _,
      Functor.id_comp _, Functor.id_comp _⟩

/-! ## The splitting criterion -/

/-- A choice of pullbacks is strict when the chosen pullback functor of a
composite is literally the composite of the chosen pullback functors. -/
def isStrictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered]
    (P : PullbackChoice p) : Prop :=
  ∀ {W V U : C} (g : W ⟶ V) (f : V ⟶ U),
    P.pullbackFunctor (g ≫ f) =
      P.pullbackFunctor f ⋙ P.pullbackFunctor g

theorem isSplitFibredCategory_iff_exists_strictPullbackChoice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibered] :
      IsSplitFibredCategory.{vC, uC, vS, uS, vS, uS} p ↔
      ∃ P : PullbackChoice p, P.IsUnital ∧ isStrictPullbackChoice P := by
  sorry

/-! ## The explicit strictification category -/

/-- An object of the category `\mathcal S'` in the proof of the strictification
lemma: an object `x` over `U`, together with an arrow `f : V ⟶ U`. -/
structure StrictificationObject
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  V : C
  U : C
  f : V ⟶ U
  x : Functor.Fiber p U

/-- The object map described in the proof of strictification sends `x` to
`(x, id_{p(x)})`. -/
def strictificationObjectOf
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    StrictificationObject p P where
  V := p.obj x
  U := p.obj x
  f := 𝟙 (p.obj x)
  x := ⟨x, rfl⟩

@[simp]
theorem strictificationObjectOf_V
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).V = p.obj x :=
  rfl

@[simp]
theorem strictificationObjectOf_U
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).U = p.obj x :=
  rfl

@[simp]
theorem strictificationObjectOf_f
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) (x : S) :
    (strictificationObjectOf P x).f = 𝟙 (p.obj x) :=
  rfl

/-- Reindexing a strictification object along `g : W ⟶ V` is the source's
object formula `(x, f) ↦ (x, f ∘ g)`. -/
def strictificationReindexObject
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W : C} (A : StrictificationObject p P) (g : W ⟶ A.V) :
    StrictificationObject p P where
  V := W
  U := A.U
  f := g ≫ A.f
  x := A.x

theorem strictificationReindexObject_comp
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W V : C} (h : W ⟶ V) (A : StrictificationObject p P)
    (g : V ⟶ A.V) :
    strictificationReindexObject
        (strictificationReindexObject A g) h =
      strictificationReindexObject A (h ≫ g) := by
  cases A
  simp [strictificationReindexObject, Category.assoc]

/-- The chosen pullback object occurring in a strictification object. -/
def strictificationPullback
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : StrictificationObject p P) : Functor.Fiber p A.V :=
  P.pullback A.f A.x

/-- A morphism in the strictification category is the underlying morphism
between the two chosen pullback objects.  Its map to the base is recovered
canonically from `p.map`; this is equivalent to the source's displayed pair
`(φ, g)` with `p(φ) = g`. -/
structure StrictificationHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {A B : StrictificationObject p P} where
  hom : (strictificationPullback A).1 ⟶ (strictificationPullback B).1

namespace StrictificationHom

@[ext]
lemma ext
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P}
    {f g : StrictificationHom (A := A) (B := B) P}
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The base arrow of a strictification morphism. -/
def base
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P}
    (f : StrictificationHom (A := A) (B := B) P) : A.V ⟶ B.V :=
  eqToHom (strictificationPullback A).2.symm ≫
    p.map f.hom ≫ eqToHom (strictificationPullback B).2

end StrictificationHom

abbrev StrictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :=
  StrictificationObject p P

instance strictificationCategory
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    Category (StrictificationCategory p P) where
  Hom A B := StrictificationHom (A := A) (B := B) P
  id A := { hom := 𝟙 (strictificationPullback A).1 }
  comp f g := { hom := f.hom ≫ g.hom }
  id_comp f := by
    apply StrictificationHom.ext
    simp
  comp_id f := by
    apply StrictificationHom.ext
    simp
  assoc f g h := by
    apply StrictificationHom.ext
    simp [Category.assoc]

/-- The projection `p' : \mathcal S' \to \mathcal C`. -/
def strictificationProjection
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    StrictificationCategory p P ⥤ C where
  obj A := A.V
  map f := StrictificationHom.base f
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

theorem strictificationProjection_isFibered
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    (strictificationProjection P).IsFibered := by
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro B R f
  let A := strictificationReindexObject B f
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
  let φ : (strictificationPullback A).1 ⟶ (strictificationPullback B).1 :=
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
  have hκbase : (strictificationProjection P).map κ = f := by
    change eqToHom _ ≫ p.map φ ≫ eqToHom _ = f
    exact (CategoryTheory.IsHomLift.fac p f φ).symm
  have hκlift : (strictificationProjection P).IsHomLift f κ := by
    have h := (inferInstance :
      (strictificationProjection P).IsHomLift
        ((strictificationProjection P).map κ) κ)
    rw [hκbase] at h
    exact h
  let : (strictificationProjection P).IsHomLift f κ := hκlift
  have hκstrong : (strictificationProjection P).IsStronglyCartesian f κ := by
    let : p.IsStronglyCartesian f φ := hφstrong
    constructor
    intro X g τ hτ
    let eX := (strictificationPullback X).2
    let eA := (strictificationPullback A).2
    let eB := (strictificationPullback B).2
    have hτmap : g ≫ f = (strictificationProjection P).map τ :=
      CategoryTheory.IsHomLift.eq_of_isHomLift
        (strictificationProjection P) (g ≫ f) τ
    have hτmap' : g ≫ f =
        eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB := by
      simpa [strictificationProjection, StrictificationHom.base] using hτmap
    let g₀ : p.obj ((strictificationPullback X).1) ⟶ R := eqToHom eX ≫ g
    have hτp : p.IsHomLift (g₀ ≫ f) τ.hom := by
      apply CategoryTheory.IsHomLift.of_fac p (g₀ ≫ f) τ.hom rfl eB
      dsimp [g₀]
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((strictificationPullback X).1)) := by
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
      rw [Category.assoc]
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
          𝟙 (p.obj ((strictificationPullback X).1)) := by
        have hd : d =
            (rfl : p.obj ((strictificationPullback X).1) =
              p.obj ((strictificationPullback X).1)) := by
          apply Subsingleton.elim
        exact congrArg
          (fun h : p.obj ((strictificationPullback X).1) =
              p.obj ((strictificationPullback X).1) => eqToHom h.symm) hd
      rw [hDom, hEq, Category.id_comp]
      rfl
    have hχbase : (strictificationProjection P).map χ' = g := by
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
    have hχ'lift : (strictificationProjection P).IsHomLift g χ' := by
      have h := (inferInstance :
        (strictificationProjection P).IsHomLift
          ((strictificationProjection P).map χ') χ')
      rw [hχbase] at h
      exact h
    let : (strictificationProjection P).IsHomLift g χ' := hχ'lift
    have hχcomp : χ' ≫ κ = τ := by
      apply StrictificationHom.ext
      exact hχfac
    refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
    intro χ'' hχ''
    have : (strictificationProjection P).IsHomLift g χ'' := hχ''.1
    have hχ''map : g = (strictificationProjection P).map χ'' := by
      exact @CategoryTheory.IsHomLift.eq_of_isHomLift C
        (StrictificationCategory p P) _ _
        (strictificationProjection P) X A g χ'' hχ''.1
    have hχ''p : p.IsHomLift g₀ χ''.hom := by
      apply CategoryTheory.IsHomLift.of_fac p g₀ χ''.hom rfl eA
      have hχ''map' : g =
          eqToHom eX.symm ≫ p.map χ''.hom ≫ eqToHom eA := by
        simpa [strictificationProjection, StrictificationHom.base] using hχ''map
      dsimp [g₀]
      rw [hχ''map']
      change p.obj ((strictificationPullback A).1) = R at eA
      have hcancel : eqToHom eX ≫ eqToHom eX.symm =
          𝟙 (p.obj ((strictificationPullback X).1)) := by
        simp
      have hcancel' := congrArg
        (fun k => k ≫ p.map χ''.hom ≫ eqToHom eA) hcancel
      convert hcancel' using 1
      rw [Category.assoc]
      rfl
    have hχ''comp : χ''.hom ≫ φ = τ.hom := by
      have hcomp := congrArg (fun h : X ⟶ B => h.hom) hχ''.2
      dsimp [κ] at hcomp
      exact hcomp
    have hhom : χ''.hom = χ :=
      hχuniq χ''.hom ⟨hχ''p, hχ''comp⟩
    exact StrictificationHom.ext hhom
  exact ⟨A, κ, hκstrong⟩

theorem strictificationProjection_isSplit
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    IsSplitFibredCategory.{vC, uC, vS, max (max uC vC) uS, vS,
      max (max uC vC) uS}
      (strictificationProjection P) := by
  sorry

theorem strictification_object_description
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (A : StrictificationObject p P) :
    (strictificationProjection P).obj A = A.V :=
  rfl

theorem strictification_morphism_description
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {A B : StrictificationObject p P} (f : A ⟶ B) :
    (strictificationProjection P).map f = StrictificationHom.base f :=
  rfl

/-! ## The strictification interface -/

/-- Equivalence in the 2-category of fibred categories over a fixed base:
the comparison functors commute strictly with the base, preserve strongly
cartesian arrows, and are inverse up to vertical natural isomorphism. -/
def IsFibredEquivalenceOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) : Prop :=
  ∃ (F : S ⥤ T) (G : T ⥤ S),
    F ⋙ q = p ∧ G ⋙ p = q ∧
      MapsStronglyCartesian p q F ∧
      MapsStronglyCartesian q p G ∧
      (∃ (e : F ⋙ G ≅ 𝟭 S)
        (over : (F ⋙ G) ⋙ p = (𝟭 S) ⋙ p),
        Formalization.Books.Categories.Unit34.IsOverNaturalIso p over e) ∧
      (∃ (e : G ⋙ F ≅ 𝟭 T)
        (over : (G ⋙ F) ⋙ q = (𝟭 T) ⋙ q),
        Formalization.Books.Categories.Unit34.IsOverNaturalIso q over e)

/-- The source's comparison data for the strictification construction.  The
first fields are the natural functor `\mathcal S \to \mathcal S'`, its
source-prescribed object map, and its strict triangle over `\mathcal C`;
the remaining fields record preservation of strongly cartesian arrows and
equivalence over the base. -/
structure StrictificationComparison
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) where
  functor : S ⥤ StrictificationCategory p P
  functor_obj : ∀ x : S, functor.obj x = strictificationObjectOf P x
  over : functor ⋙ strictificationProjection P = p
  preserves : MapsStronglyCartesian p (strictificationProjection P) functor
  inverse : StrictificationCategory p P ⥤ S
  inverse_over : inverse ⋙ p = strictificationProjection P
  inverse_preserves :
    MapsStronglyCartesian (strictificationProjection P) p inverse
  functor_inverse :
    ∃ (e : functor ⋙ inverse ≅ 𝟭 S)
      (over : (functor ⋙ inverse) ⋙ p = (𝟭 S) ⋙ p),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso p over e
  inverse_functor :
    ∃ (e : inverse ⋙ functor ≅ 𝟭 (StrictificationCategory p P))
      (over : (inverse ⋙ functor) ⋙ strictificationProjection P =
        (𝟭 (StrictificationCategory p P)) ⋙ strictificationProjection P),
      Formalization.Books.Categories.Unit34.IsOverNaturalIso
        (strictificationProjection P) over e

theorem strictificationComparison_isFibredEquivalence
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    (D : StrictificationComparison p P) :
    IsFibredEquivalenceOver p (strictificationProjection P) := by
  exact ⟨D.functor, D.inverse, D.over, D.inverse_over, D.preserves,
    D.inverse_preserves, D.functor_inverse, D.inverse_functor⟩

def strictificationInverse
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    StrictificationCategory p P ⥤ S where
  obj A := (strictificationPullback A).1
  map f := f.hom
  map_id _ := rfl
  map_comp f g := rfl

def strictificationFunctorHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {x y : S} (φ : x ⟶ y) :
    StrictificationHom (P := P)
      (A := strictificationObjectOf P x) (B := strictificationObjectOf P y) where
  hom := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
    (𝟙 (p.obj y))
    (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩)
    (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj y)) ⟨y, rfl⟩)
    _ _ (p.map φ) (p.map φ) (by simp)
    (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ)
    (by
      letI : p.IsStronglyCartesian (𝟙 (p.obj x))
          (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
        P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩
      change p.IsHomLift (p.map φ)
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ φ)
      simpa using (IsHomLift.comp p (𝟙 (p.obj x)) (p.map φ)
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) φ))

theorem strictificationFunctorHom_isHomLift
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    {x y : S} (φ : x ⟶ y) :
  p.IsHomLift (p.map φ) (strictificationFunctorHom P φ).hom := by
  unfold strictificationFunctorHom
  letI : p.IsStronglyCartesian (𝟙 (p.obj y))
      (P.pullbackMap (𝟙 (p.obj y)) ⟨y, rfl⟩) :=
    P.pullbackMap_isStronglyCartesian _ _
  letI : p.IsStronglyCartesian (𝟙 (p.obj x))
      (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
    P.pullbackMap_isStronglyCartesian _ _
  letI : p.IsHomLift (p.map φ)
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

def strictificationFunctor
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    S ⥤ StrictificationCategory p P where
  obj x := strictificationObjectOf P x
  map φ := strictificationFunctorHom P φ
  map_id x := by
    apply StrictificationHom.ext
    change (strictificationFunctorHom P (𝟙 x)).hom = 𝟙 _
    letI : p.IsStronglyCartesian (𝟙 (p.obj x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) :=
      P.pullbackMap_isStronglyCartesian (𝟙 (p.obj x)) ⟨x, rfl⟩
    let hsource' : p.IsHomLift (p.map (𝟙 x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩ ≫ 𝟙 x) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj x)) (p.map (𝟙 x))
        (P.pullbackMap (𝟙 (p.obj x)) ⟨x, rfl⟩) (𝟙 x))
    let hψ : p.IsHomLift (p.map (𝟙 x))
        (strictificationFunctorHom P (𝟙 x)).hom := by
      exact strictificationFunctorHom_isHomLift P (𝟙 x)
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
      (p.map (𝟙 x)) (strictificationFunctorHom P (𝟙 x)).hom (𝟙 _)
      hψ hψ' (by
        have hfac : (strictificationFunctorHom P (𝟙 x)).hom ≫
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
    apply StrictificationHom.ext
    change (strictificationFunctorHom P (f ≫ g)).hom =
      (strictificationFunctorHom P f).hom ≫
        (strictificationFunctorHom P g).hom
    let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
    let xY : Functor.Fiber p (p.obj Y) := ⟨Y, rfl⟩
    let xZ : Functor.Fiber p (p.obj Z) := ⟨Z, rfl⟩
    let uX := P.pullbackMap (𝟙 (p.obj X)) xX
    let uY := P.pullbackMap (𝟙 (p.obj Y)) xY
    let uZ := P.pullbackMap (𝟙 (p.obj Z)) xZ
    letI : p.IsStronglyCartesian (𝟙 (p.obj Z))
        uZ := P.pullbackMap_isStronglyCartesian _ _
    letI : p.IsStronglyCartesian (𝟙 (p.obj Y))
        uY := P.pullbackMap_isStronglyCartesian _ _
    letI : p.IsStronglyCartesian (𝟙 (p.obj X))
        uX := P.pullbackMap_isStronglyCartesian _ _
    have hsource_fg : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map (f ≫ g))
        uX (f ≫ g))
    letI : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := hsource_fg
    letI : p.IsHomLift (p.map f)
        (strictificationFunctorHom P f).hom :=
      strictificationFunctorHom_isHomLift P f
    letI : p.IsHomLift (p.map g)
        (strictificationFunctorHom P g).hom :=
      strictificationFunctorHom_isHomLift P g
    letI : p.IsHomLift (p.map f ≫ p.map g)
        (uX ≫ (f ≫ g)) := by
      simpa only [Functor.map_comp] using
        (show p.IsHomLift (p.map (f ≫ g))
          (uX ≫ (f ≫ g)) by infer_instance)
    have hcompActual : p.IsHomLift (p.map f ≫ p.map g)
        (strictificationFunctorHom P (f ≫ g)).hom := by
      have h := strictificationFunctorHom_isHomLift P (f ≫ g)
      rw [p.map_comp] at h
      exact h
    have hcomp : p.IsHomLift (p.map f ≫ p.map g)
        ((strictificationFunctorHom P f).hom ≫
          (strictificationFunctorHom P g).hom) := by
      exact IsHomLift.comp p (p.map f) (p.map g)
        (strictificationFunctorHom P f).hom
        (strictificationFunctorHom P g).hom
    have hsource_f : p.IsHomLift (p.map f) (uX ≫ f) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map f)
        uX f)
    have hsource_g : p.IsHomLift (p.map g) (uY ≫ g) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj Y)) (p.map g)
        uY g)
    have hfac_fg :
        (strictificationFunctorHom P (f ≫ g)).hom ≫
            uZ = uX ≫ (f ≫ g) := by
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
        (strictificationFunctorHom P f).hom ≫
            uY = uX ≫ f := by
      change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Y)) uY
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
        _ _ (p.map f) (p.map f) (by simp)
        (uX ≫ f) hsource_f) ≫ uY = _
      simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Y)) uY
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
        (p.obj X) (Functor.Fiber.fiberInclusion.obj
          (P.pullback (𝟙 (p.obj X)) xX))
        (p.map f) (p.map f) (by simp)
        (uX ≫ f) hsource_f)
    have hfac_g :
        (strictificationFunctorHom P g).hom ≫
            uZ = uY ≫ g := by
      change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        _ _ (p.map g) (p.map g) (by simp)
        (uY ≫ g) hsource_g) ≫ uZ = _
      simpa only using (@Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
        (𝟙 (p.obj Z)) uZ
        (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
        (p.obj Y) (Functor.Fiber.fiberInclusion.obj (P.pullback (𝟙 (p.obj Y)) xY))
        (p.map g) (p.map g) (by simp)
        (uY ≫ g) hsource_g)
    have hEq :
        (strictificationFunctorHom P (f ≫ g)).hom ≫
            uZ =
          ((strictificationFunctorHom P f).hom ≫
            (strictificationFunctorHom P g).hom) ≫
              uZ := by
      dsimp [xX, xY, xZ, uX, uY, uZ] at hfac_fg hfac_f hfac_g ⊢
      exact hfac_fg.trans <|
        (Category.assoc uX f g).symm.trans <|
          (congrArg (fun k => k ≫ g) hfac_f.symm).trans <|
            (Category.assoc (strictificationFunctorHom P f).hom uY g).trans <|
              (congrArg (fun k => (strictificationFunctorHom P f).hom ≫ k)
                hfac_g.symm).trans <|
                (Category.assoc (strictificationFunctorHom P f).hom
                  (strictificationFunctorHom P g).hom uZ).symm
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (𝟙 (p.obj Z)) uZ
      (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ)
      (p.obj X) (Functor.Fiber.fiberInclusion.obj
        (P.pullback (𝟙 (p.obj X)) xX)) (p.map f ≫ p.map g)
      (strictificationFunctorHom P (f ≫ g)).hom
      ((strictificationFunctorHom P f).hom ≫
        (strictificationFunctorHom P g).hom)
      hcompActual hcomp hEq

theorem strictification_comparison_exists
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) [p.IsFibered] (P : PullbackChoice p) :
    Nonempty (StrictificationComparison p P) := by
  refine ⟨{
    functor := strictificationFunctor P
    functor_obj := by intro x; rfl
    over := by
      refine CategoryTheory.Functor.hext (fun x => rfl) ?_
      intro x y f
      letI : p.IsHomLift (p.map f) (strictificationFunctorHom P f).hom :=
        strictificationFunctorHom_isHomLift P f
      simpa [strictificationFunctor, strictificationProjection,
        StrictificationHom.base] using
        heq_of_eq ((CategoryTheory.IsHomLift.fac p (p.map f)
          (strictificationFunctorHom P f).hom).symm)
    preserves := by
      intro X Y φ hφ
      let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
      let xY : Functor.Fiber p (p.obj Y) := ⟨Y, rfl⟩
      let uX := P.pullbackMap (𝟙 (p.obj X)) xX
      let uY := P.pullbackMap (𝟙 (p.obj Y)) xY
      let h := (strictificationFunctorHom P φ).hom
      have huX : p.IsStronglyCartesian (𝟙 (p.obj X)) uX := by
        exact P.pullbackMap_isStronglyCartesian _ _
      have huY : p.IsStronglyCartesian (𝟙 (p.obj Y)) uY := by
        exact P.pullbackMap_isStronglyCartesian _ _
      have hsource : p.IsHomLift (p.map φ) (uX ≫ φ) := by
        simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map φ) uX φ)
      have hhomLift : p.IsHomLift (p.map φ) h := by
        exact strictificationFunctorHom_isHomLift P φ
      have hfac : h ≫ uY = uX ≫ φ := by
        change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
          (𝟙 (p.obj Y)) uY huY _ _ (p.map φ) (p.map φ) (by simp)
          (uX ≫ φ) hsource) ≫ uY = _
        exact Functor.IsStronglyCartesian.fac p (𝟙 (p.obj Y)) uY
          (f' := p.map φ) (g := p.map φ) (by simp) (uX ≫ φ)
      have hcompStrong : p.IsStronglyCartesian (p.map φ) (h ≫ uY) := by
        change p.IsStronglyCartesian (p.map φ)
          ((strictificationFunctorHom P φ).hom ≫ uY)
        rw [hfac]
        dsimp [uX, xX, strictificationPullback, strictificationObjectOf]
        simpa [strictificationPullback, strictificationObjectOf, xX, xY,
          Functor.Fiber.fiberInclusion] using
          (@Functor.IsStronglyCartesian.comp _ _ _ _ p _ _ _ _
          _ _ (𝟙 (p.obj X)) (p.map φ) uX φ huX hφ)
      have hstrong : p.IsStronglyCartesian (p.map φ) h := by
        letI : p.IsHomLift (p.map φ) h := hhomLift
        letI : p.IsStronglyCartesian (p.map φ ≫ 𝟙 (p.obj Y))
            (h ≫ uY) := by simpa using hcompStrong
        letI : p.IsStronglyCartesian (𝟙 (p.obj Y)) uY := huY
        exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _
          (p.map φ) (𝟙 (p.obj Y)) h uY huY
          (by simpa using hcompStrong) hhomLift
      letI : p.IsStronglyCartesian (p.map φ) h := hstrong
      letI : p.IsHomLift (p.map φ) h := hhomLift
      let q := strictificationProjection P
      letI : (strictificationProjection P).IsFibered :=
        strictificationProjection_isFibered P
      let κ : (strictificationFunctor P).obj X ⟶
          (strictificationFunctor P).obj Y := strictificationFunctorHom P φ
      have hqmap : q.map κ = p.map φ := by
        dsimp [q, κ, strictificationProjection, StrictificationHom.base,
          h]
        exact (CategoryTheory.IsHomLift.fac p (p.map φ) h).symm
      letI : q.IsHomLift (q.map κ) κ := by
        exact Functor.IsHomLift.map κ
      have hκstrong : (strictificationProjection P).IsStronglyCartesian
          (q.map κ) κ := by
        constructor
        intro Z g τ hτ
        let eZ := (strictificationPullback Z).2
        let eX := (strictificationPullback ((strictificationFunctor P).obj X)).2
        let eY := (strictificationPullback ((strictificationFunctor P).obj Y)).2
        change p.obj ((strictificationPullback ((strictificationFunctor P).obj X)).1) =
          p.obj X at eX
        change p.obj ((strictificationPullback ((strictificationFunctor P).obj Y)).1) =
          p.obj Y at eY
        have hτmap : g ≫ q.map κ = q.map τ :=
          CategoryTheory.IsHomLift.eq_of_isHomLift q (g ≫ q.map κ) τ
        have hτmap' : g ≫ p.map φ =
            eqToHom eZ.symm ≫ p.map τ.hom ≫ eqToHom eY := by
          rw [hqmap] at hτmap
          simpa [q, strictificationFunctor, strictificationProjection,
            StrictificationHom.base] using hτmap
        let g₀ : p.obj ((strictificationPullback Z).1) ⟶
            p.obj X :=
          eqToHom eZ ≫ g
        have hτp : p.IsHomLift (g₀ ≫ p.map φ) τ.hom := by
          apply CategoryTheory.IsHomLift.of_fac p (g₀ ≫ p.map φ)
            τ.hom rfl eY
          dsimp [g₀]
          have hcancel : eqToHom eZ ≫ eqToHom eZ.symm =
              𝟙 (p.obj ((strictificationPullback Z).1)) := by simp
          have hAssoc : (eqToHom eZ ≫ g) ≫ p.map φ =
              eqToHom eZ ≫ (g ≫ p.map φ) := Category.assoc _ _ _
          have hRewrite : eqToHom eZ ≫ (g ≫ p.map φ) =
              eqToHom eZ ≫
                (eqToHom eZ.symm ≫ p.map τ.hom ≫ eqToHom eY) := by
            exact congrArg (fun k => eqToHom eZ ≫ k) hτmap'
          have hcancel' := congrArg
            (fun k => k ≫ p.map τ.hom ≫ eqToHom eY) hcancel
          change (eqToHom eZ ≫ g) ≫ p.map φ =
            𝟙 (p.obj ((strictificationPullback Z).1)) ≫
              p.map τ.hom ≫ eqToHom eY
          rw [hAssoc, hRewrite]
          convert hcancel' using 1
          rw [Category.assoc]
        obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
          @Functor.IsStronglyCartesian.universal_property _ _ _ _ p
            _ _ _ _ (p.map φ) h hstrong _ _ g₀ (g₀ ≫ p.map φ)
            rfl τ.hom hτp
        let χ' : Z ⟶ (strictificationFunctor P).obj X := { hom := χ }
        have hχbase : q.map χ' = g := by
          change eqToHom eZ.symm ≫ p.map χ ≫ eqToHom eX = g
          have hχfac' : g₀ = p.map χ ≫ eqToHom eX := by
            simpa [g₀, strictificationFunctor] using
              (CategoryTheory.IsHomLift.fac p g₀ χ)
          rw [← hχfac']
          change Z.V ⟶ ((strictificationFunctor P).obj X).V at g
          dsimp [g₀]
          have hcancel : eqToHom eZ.symm ≫ eqToHom eZ =
              𝟙 Z.V := by simp
          calc
            eqToHom eZ.symm ≫ eqToHom eZ ≫ g =
                (eqToHom eZ.symm ≫ eqToHom eZ) ≫ g :=
              (Category.assoc _ _ _).symm
            _ = (𝟙 Z.V) ≫ g := congrArg (fun k => k ≫ g) hcancel
            _ = g := by simp
        letI : q.IsHomLift g χ' := by
          have h := (Functor.IsHomLift.map (p := q) χ')
          rw [hχbase] at h
          exact h
        have hχcomp : χ' ≫ κ = τ := by
          apply StrictificationHom.ext
          exact hχfac
        refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
        intro χ'' hχ''
        letI : q.IsHomLift g χ'' := hχ''.1
        have hχ''map : g = q.map χ'' :=
          CategoryTheory.IsHomLift.eq_of_isHomLift q g χ''
        have hχ''p : p.IsHomLift g₀ χ''.hom := by
          apply CategoryTheory.IsHomLift.of_fac p g₀ χ''.hom rfl eX
          have hχ''map' : g =
              eqToHom eZ.symm ≫ p.map χ''.hom ≫ eqToHom eX := by
            simpa [q, strictificationFunctor, strictificationProjection,
              StrictificationHom.base] using hχ''map
          dsimp [g₀]
          rw [hχ''map']
          have hcancel : eqToHom eZ ≫ eqToHom eZ.symm =
              𝟙 (p.obj ((strictificationPullback Z).1)) := by simp
          have hcancel' := congrArg
            (fun k => k ≫ p.map χ''.hom ≫ eqToHom eX) hcancel
          convert hcancel' using 1
          rw [Category.assoc]
        have hχ''comp : χ''.hom ≫ h = τ.hom := by
          exact congrArg (fun k : Z ⟶ (strictificationFunctor P).obj Y => k.hom)
            hχ''.2
        exact StrictificationHom.ext (hχuniq χ''.hom ⟨hχ''p, hχ''comp⟩)
      change (strictificationProjection P).IsStronglyCartesian
        (q.map κ) κ
      exact hκstrong
    inverse := strictificationInverse P
    inverse_over := by
      refine CategoryTheory.Functor.hext
        (fun A => (strictificationPullback A).2) ?_
      intro A B f
      simpa [strictificationInverse] using
        (CategoryTheory.conj_eqToHom_iff_heq' (p.map f.hom)
          ((strictificationProjection P).map f)
          (strictificationPullback A).2
          (strictificationPullback B).2.symm).mp (by
            simp [strictificationProjection, StrictificationHom.base,
              Category.assoc])
    inverse_preserves := by
      intro A B f hf
      let q := strictificationProjection P
      letI : q.IsFibered := strictificationProjection_isFibered P
      letI : q.IsStronglyCartesian (q.map f) f := hf
      let eA := (strictificationPullback A).2
      let eB := (strictificationPullback B).2
      change p.obj ((strictificationInverse P).obj A) = A.V at eA
      change p.obj ((strictificationInverse P).obj B) = B.V at eB
      constructor
      intro Z g τ hτ
      let xZ : Functor.Fiber p (p.obj Z) := ⟨Z, rfl⟩
      let K : StrictificationObject p P := {
        V := p.obj Z
        U := p.obj Z
        f := 𝟙 (p.obj Z)
        x := xZ }
      let eK := (strictificationPullback K).2
      change p.obj ((strictificationPullback K).1) = p.obj Z at eK
      change p.obj (P.pullback (𝟙 (p.obj Z)) xZ).1 = p.obj Z at eK
      let uZ := P.pullbackMap (𝟙 (p.obj Z)) xZ
      change (P.pullback (𝟙 (p.obj Z)) xZ).1 ⟶ Z at uZ
      letI : p.IsStronglyCartesian (𝟙 (p.obj Z)) uZ :=
        P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ
      change p.IsHomLift (g ≫ p.map f.hom) τ at hτ
      letI : p.IsHomLift (g ≫ p.map f.hom) τ := hτ
      let G : q.obj K ⟶ q.obj A := by
        change p.obj Z ⟶ A.V
        exact g ≫ eqToHom eA
      let δ : K ⟶ B := by
        dsimp [K]
        exact { hom := uZ ≫ τ }
      have hτmap : g ≫ p.map f.hom = p.map τ :=
        @CategoryTheory.IsHomLift.eq_of_isHomLift C S _ _ p Z
          ((strictificationInverse P).obj B) (g ≫ p.map f.hom) τ hτ
      have hδmap : G ≫ q.map f = q.map δ := by
        have huZmap : p.map uZ = eqToHom eK := by
          have hfac := CategoryTheory.IsHomLift.fac p
            (𝟙 (p.obj Z)) uZ
          have hfac' : 𝟙 (p.obj Z) =
              eqToHom eK.symm ≫ p.map uZ := by
            simpa [Category.assoc] using hfac
          have hfac'' := congrArg (fun k => eqToHom eK ≫ k) hfac'
          simpa [Category.assoc] using hfac''.symm
        have hA : eqToHom eA ≫ eqToHom eA.symm =
            𝟙 (p.obj ((strictificationInverse P).obj A)) := by simp
        have hK : eqToHom eK.symm ≫ p.map uZ =
            𝟙 (p.obj Z) := by rw [huZmap]; simp
        have hKτ := congrArg
          (fun k => k ≫ p.map τ ≫ eqToHom eB) hK
        change (g ≫ eqToHom eA) ≫
            (eqToHom eA.symm ≫ p.map f.hom ≫ eqToHom eB) =
          eqToHom eK.symm ≫ p.map (uZ ≫ τ) ≫ eqToHom eB
        calc
          (g ≫ eqToHom eA) ≫
              (eqToHom eA.symm ≫ p.map f.hom ≫ eqToHom eB) =
              (g ≫ p.map f.hom) ≫ eqToHom eB := by
            simp [Category.assoc, hA]
          _ = p.map τ ≫ eqToHom eB :=
            congrArg (fun k => k ≫ eqToHom eB) hτmap
          _ = eqToHom eK.symm ≫ p.map (uZ ≫ τ) ≫ eqToHom eB := by
            rw [Functor.map_comp]
            simpa [Category.assoc] using hKτ.symm
      have hδlift : q.IsHomLift (G ≫ q.map f) δ := by
        rw [hδmap]
        exact Functor.IsHomLift.map δ
      obtain ⟨χ, ⟨hχ, hχfac⟩, hχuniq⟩ :=
        @Functor.IsStronglyCartesian.universal_property _ _ _ _ q
          _ _ _ _ (q.map f) f hf _ _ G (G ≫ q.map f) rfl δ hδlift
      letI : IsIso uZ :=
        Functor.IsStronglyCartesian.isIso_of_base_isIso p
          (𝟙 (p.obj Z)) uZ
      have huZmap : p.map uZ = eqToHom eK := by
        have hfac := CategoryTheory.IsHomLift.fac p
          (𝟙 (p.obj Z)) uZ
        have hfac' : 𝟙 (p.obj Z) =
            eqToHom eK.symm ≫ p.map uZ := by
          simpa [Category.assoc] using hfac
        have hfac'' := congrArg (fun k => eqToHom eK ≫ k) hfac'
        simpa [Category.assoc] using hfac''.symm
      let vZ := (asIso uZ).inv
      have hvZmap : p.map vZ = eqToHom eK.symm := by
        have hv : p.map vZ ≫ p.map uZ = 𝟙 (p.obj Z) := by
          simpa [vZ] using congrArg p.map (asIso uZ).inv_hom_id
        rw [huZmap] at hv
        apply (cancel_mono (eqToHom eK)).1
        simpa [Category.assoc] using hv
      letI : q.IsHomLift G χ := hχ
      have hχmap : q.map χ = G :=
        (CategoryTheory.IsHomLift.eq_of_isHomLift q G χ).symm
      have hχmap' :
          eqToHom eK.symm ≫ p.map χ.hom ≫ eqToHom eA =
            g ≫ eqToHom eA := by
        change q.map χ = G at hχmap
        change eqToHom eK.symm ≫ p.map χ.hom ≫ eqToHom eA =
          g ≫ eqToHom eA at hχmap
        exact hχmap
      have hχmap'' : eqToHom eK.symm ≫ p.map χ.hom = g := by
        apply (cancel_mono (eqToHom eA)).1
        rw [← Category.assoc] at hχmap'
        exact hχmap'
      let δp : Z ⟶ (strictificationInverse P).obj A :=
        vZ ≫ χ.hom
      have hδpmap : p.map δp = g := by
        dsimp [δp]
        have hcomp : p.map (vZ ≫ χ.hom) =
            p.map vZ ≫ p.map χ.hom := by
          simpa [K] using (p.map_comp vZ χ.hom)
        have hrest : p.map vZ ≫ p.map χ.hom = g := by
          rw [hvZmap]
          exact hχmap''
        exact hcomp.trans hrest
      have hδplift : p.IsHomLift g δp := by
        apply CategoryTheory.IsHomLift.of_fac' p g δp rfl rfl
        simpa using hδpmap
      have hχfac' : χ.hom ≫ f.hom = uZ ≫ τ := by
        have h := congrArg (fun k : K ⟶ B => k.hom) hχfac
        change χ.hom ≫ f.hom = uZ ≫ τ at h
        exact h
      have hδpcomp : δp ≫ f.hom = τ := by
        dsimp [δp]
        have hleft : (vZ ≫ χ.hom) ≫ f.hom = vZ ≫ (uZ ≫ τ) := by
          exact (Category.assoc vZ χ.hom f.hom).trans
            (congrArg (fun k => vZ ≫ k) hχfac')
        exact hleft.trans ((asIso uZ).inv_hom_id_assoc τ)
      refine ⟨δp, ⟨hδplift, hδpcomp⟩, ?_⟩
      intro δ' hδ'
      letI : p.IsHomLift g δ' := hδ'.1
      have hδ'map : p.map δ' = g :=
        (CategoryTheory.IsHomLift.eq_of_isHomLift p g δ').symm
      let χ' : K ⟶ A := { hom := uZ ≫ δ' }
      have hχ'map_base :
          eqToHom eK.symm ≫ p.map (uZ ≫ δ') ≫ eqToHom eA =
            g ≫ eqToHom eA := by
        rw [Functor.map_comp, huZmap, hδ'map]
        simp [Category.assoc]
      have hχ'map : q.map χ' = G := by
        change q.map χ' = G
        change eqToHom eK.symm ≫ p.map (uZ ≫ δ') ≫ eqToHom eA =
          g ≫ eqToHom eA
        exact hχ'map_base
      have hχ'lift : q.IsHomLift G χ' := by
        apply CategoryTheory.IsHomLift.of_fac' q G χ' rfl rfl
        simpa [q] using hχ'map
      have hχ'comp : χ' ≫ f = δ := by
        apply StrictificationHom.ext
        change (uZ ≫ δ') ≫ f.hom = uZ ≫ τ
        have hδ'comp : δ' ≫ f.hom = τ := by
          have h := hδ'.2
          change δ' ≫ f.hom = τ at h
          exact h
        have hleft : (uZ ≫ δ') ≫ f.hom = uZ ≫ τ := by
          exact (Category.assoc uZ δ' f.hom).trans
            (congrArg (fun k => uZ ≫ k) hδ'comp)
        exact hleft
      have hχ'eq : χ' = χ :=
        hχuniq χ' ⟨hχ'lift, hχ'comp⟩
      have hχhom : uZ ≫ δ' = χ.hom :=
        congrArg (fun k : K ⟶ A => k.hom) hχ'eq
      apply (cancel_epi uZ).1
      rw [hχhom]
      dsimp [δp]
      exact ((asIso uZ).hom_inv_id_assoc χ.hom).symm
    functor_inverse := by
      let comp := strictificationFunctor P ⋙ strictificationInverse P
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
          have hfac : (strictificationFunctorHom P f).hom ≫ uY =
              uX ≫ f := by
            change (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
              (𝟙 (p.obj Y)) uY
              (P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Y)) xY)
              _ _ (p.map f) (p.map f) (by simp)
              (uX ≫ f) _) ≫ uY = uX ≫ f
            exact Functor.IsStronglyCartesian.fac p (𝟙 (p.obj Y)) uY
              (f' := p.map f) (g := p.map f) (by simp) (uX ≫ f)
          exact hfac)
      refine ⟨e, ?_, ?_⟩
      · refine CategoryTheory.Functor.hext
          (fun X => (strictificationPullback
            (strictificationObjectOf P X)).2) ?_
        intro X Y f
        letI : p.IsHomLift (p.map f)
            (strictificationFunctorHom P f).hom :=
          strictificationFunctorHom_isHomLift P f
        let eX := (strictificationPullback (strictificationObjectOf P X)).2
        let eY := (strictificationPullback (strictificationObjectOf P Y)).2
        have hfac : p.map f =
            eqToHom eX.symm ≫ p.map (strictificationFunctorHom P f).hom ≫
              eqToHom eY := by
          simpa [strictificationFunctor, strictificationProjection,
            StrictificationHom.base] using
            (CategoryTheory.IsHomLift.fac p (p.map f)
              (strictificationFunctorHom P f).hom)
        exact ((CategoryTheory.conj_eqToHom_iff_heq'
          (p.map f) (p.map (strictificationFunctorHom P f).hom)
          eX.symm eY).mp (by
            simpa [Category.assoc] using hfac)).symm
      · intro X
        let xX : Functor.Fiber p (p.obj X) := ⟨X, rfl⟩
        let eX := (strictificationPullback
          (strictificationObjectOf P X)).2
        change p.obj (P.pullback (𝟙 (p.obj X)) xX).1 = p.obj X at eX
        let uX := P.pullbackMap (𝟙 (p.obj X)) xX
        change (P.pullback (𝟙 (p.obj X)) xX).1 ⟶ X at uX
        letI : p.IsStronglyCartesian (𝟙 (p.obj X)) uX :=
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
    inverse_functor := by
      let comp := strictificationInverse P ⋙ strictificationFunctor P
      let component : ∀ A : StrictificationCategory p P, comp.obj A ≅ A := by
        intro A
        let xA : Functor.Fiber p
            (p.obj ((strictificationPullback A).1)) :=
          ⟨(strictificationPullback A).1, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((strictificationPullback A).1))) xA
        change (P.pullback
          (𝟙 (p.obj ((strictificationPullback A).1))) xA).1 ⟶
          (strictificationPullback A).1 at wA
        letI : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationPullback A).1))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        letI : IsIso wA :=
          Functor.IsStronglyCartesian.isIso_of_base_isIso p
            (𝟙 (p.obj ((strictificationPullback A).1))) wA
        dsimp [comp, strictificationFunctor, strictificationInverse]
        dsimp [xA] at wA ⊢
        let vA : (strictificationPullback A).1 ⟶
            (P.pullback
              (𝟙 (p.obj ((strictificationPullback A).1))) xA).1 :=
          (asIso wA).inv
        let κ : comp.obj A ⟶ A := by
          dsimp [comp, strictificationFunctor, strictificationInverse]
          exact { hom := wA }
        let κinv : A ⟶ comp.obj A := by
          dsimp [comp, strictificationFunctor, strictificationInverse]
          exact { hom := vA }
        refine { hom := κ, inv := κinv, hom_inv_id := ?_, inv_hom_id := ?_ }
        · apply StrictificationHom.ext
          change wA ≫ vA = 𝟙 _
          exact (asIso wA).hom_inv_id
        · apply StrictificationHom.ext
          change vA ≫ wA = 𝟙 _
          exact (asIso wA).inv_hom_id
      let e : comp ≅ 𝟭 (StrictificationCategory p P) :=
        NatIso.ofComponents component (fun {A B} f => by
          apply StrictificationHom.ext
          let xA : Functor.Fiber p (p.obj ((strictificationInverse P).obj A)) :=
            ⟨(strictificationInverse P).obj A, rfl⟩
          let xB : Functor.Fiber p (p.obj ((strictificationInverse P).obj B)) :=
            ⟨(strictificationInverse P).obj B, rfl⟩
          let wA := P.pullbackMap
            (𝟙 (p.obj ((strictificationInverse P).obj A))) xA
          let wB := P.pullbackMap
            (𝟙 (p.obj ((strictificationInverse P).obj B))) xB
          letI : p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationPullback A).1))) wA := by
            change p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
            exact P.pullbackMap_isStronglyCartesian _ _
          letI : p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationPullback B).1))) wB := by
            change p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationInverse P).obj B))) wB
            exact P.pullbackMap_isStronglyCartesian _ _
          letI : p.IsHomLift (p.map f.hom) f.hom := by
            apply CategoryTheory.IsHomLift.of_fac' p
              (p.map f.hom) f.hom rfl rfl
            simp
          have hsource0 : p.IsHomLift
              (𝟙 (p.obj ((strictificationPullback A).1)) ≫ p.map f.hom)
              (wA ≫ f.hom) := by
            exact @CategoryTheory.IsHomLift.comp _ _ _ _ p
              _ _ _ _ _ _
              (𝟙 (p.obj ((strictificationPullback A).1)))
              (p.map f.hom) wA f.hom
              (inferInstance : p.IsHomLift
                (𝟙 (p.obj ((strictificationPullback A).1))) wA)
              (inferInstance : p.IsHomLift (p.map f.hom) f.hom)
          have hsource : p.IsHomLift (p.map f.hom) (wA ≫ f.hom) := by
            simpa using hsource0
          letI : p.IsHomLift (p.map f.hom) (wA ≫ f.hom) := hsource
          letI : p.IsHomLift
              (p.map f.hom ≫ 𝟙 (p.obj ((strictificationPullback B).1)))
              (wA ≫ f.hom) := by
            simpa using hsource
          have hfac : (strictificationFunctorHom P f.hom).hom ≫ wB =
              wA ≫ f.hom := by
            exact @Functor.IsStronglyCartesian.fac _ _ _ _ p _ _ _ _
              (𝟙 (p.obj ((strictificationPullback B).1))) wB
              (P.pullbackMap_isStronglyCartesian
                (𝟙 (p.obj ((strictificationInverse P).obj B))) xB)
              (p.obj ((strictificationPullback A).1))
              (Functor.Fiber.fiberInclusion.obj
                (P.pullback
                  (𝟙 (p.obj ((strictificationInverse P).obj A))) xA))
              (p.map f.hom) (p.map f.hom) (by simp)
              (wA ≫ f.hom) hsource
          dsimp [comp, component]
          change (strictificationFunctorHom P f.hom).hom ≫ wB =
            wA ≫ f.hom
          exact hfac)
      refine ⟨e, ?_, ?_⟩
      · refine CategoryTheory.Functor.hext
          (fun A => (strictificationPullback A).2) ?_
        intro A B f
        let xA : Functor.Fiber p
            (p.obj ((strictificationInverse P).obj A)) :=
          ⟨(strictificationInverse P).obj A, rfl⟩
        let xB : Functor.Fiber p
            (p.obj ((strictificationInverse P).obj B)) :=
          ⟨(strictificationInverse P).obj B, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((strictificationInverse P).obj A))) xA
        let wB := P.pullbackMap
          (𝟙 (p.obj ((strictificationInverse P).obj B))) xB
        have hfac : (strictificationFunctorHom P f.hom).hom ≫ wB =
            wA ≫ f.hom := by
          have h := congrArg (fun k => k.hom) (e.hom.naturality f)
          dsimp [e, NatIso.ofComponents, component, comp] at h
          exact h
        let eA' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
        let eB' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((strictificationInverse P).obj B))) wB
        let eA0 : p.obj ((strictificationInverse P).obj A) = A.V := by
          change p.obj ((strictificationPullback A).1) = A.V
          exact (strictificationPullback A).2
        let eB0 : p.obj ((strictificationInverse P).obj B) = B.V := by
          change p.obj ((strictificationPullback B).1) = B.V
          exact (strictificationPullback B).2
        letI : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        letI : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj B))) wB :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
          convert h using 1 <;>
            simp [eA', strictificationObjectOf, strictificationPullback]
        have hwB : p.map wB = eqToHom eB' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj B))) wB
          convert h using 1 <;>
            simp [eB', strictificationObjectOf, strictificationPullback]
        have hfacMap :
            p.map (strictificationFunctorHom P f.hom).hom ≫
                p.map wB = p.map wA ≫ p.map f.hom := by
          have h := congrArg p.map hfac
          have h1 := p.map_comp
            (strictificationFunctorHom P f.hom).hom wB
          have h2 := p.map_comp wA f.hom
          exact h1.symm.trans (h.trans h2)
        have hmap :
            p.map (strictificationFunctorHom P f.hom).hom ≫
                eqToHom eB' = eqToHom eA' ≫ p.map f.hom := by
          have hB := congrArg
            (fun k => p.map (strictificationFunctorHom P f.hom).hom ≫ k) hwB
          have hA := congrArg (fun k => k ≫ p.map f.hom) hwA
          exact hB.symm.trans (hfacMap.trans hA)
        have hconj :
            (strictificationProjection P).map f =
              eqToHom (strictificationPullback A).2.symm ≫
                (strictificationProjection P).map
                  (strictificationFunctorHom P f.hom) ≫
                eqToHom (strictificationPullback B).2 := by
          change eqToHom eA0.symm ≫ p.map f.hom ≫ eqToHom eB0 =
            eqToHom eA0.symm ≫
              (eqToHom eA'.symm ≫ p.map
                (strictificationFunctorHom P f.hom).hom ≫
                eqToHom eB') ≫ eqToHom eB0
          calc
            eqToHom eA0.symm ≫ p.map f.hom ≫ eqToHom eB0 =
                eqToHom eA0.symm ≫ eqToHom eA'.symm ≫
                  (eqToHom eA' ≫ p.map f.hom) ≫ eqToHom eB0 := by
              simp [Category.assoc]
            _ = eqToHom eA0.symm ≫ eqToHom eA'.symm ≫
                  (p.map (strictificationFunctorHom P f.hom).hom ≫
                    eqToHom eB') ≫ eqToHom eB0 := by
              have hstep := congrArg
                (fun k => eqToHom eA0.symm ≫ eqToHom eA'.symm ≫ k ≫
                  eqToHom eB0) hmap
              exact hstep.symm
            _ = eqToHom eA0.symm ≫
                  (eqToHom eA'.symm ≫ p.map
                    (strictificationFunctorHom P f.hom).hom ≫
                    eqToHom eB') ≫ eqToHom eB0 := by
              simp [Category.assoc]
        have hheq := (CategoryTheory.conj_eqToHom_iff_heq'
            ((strictificationProjection P).map f)
            ((strictificationProjection P).map
              (strictificationFunctorHom P f.hom))
            (strictificationPullback A).2.symm
            (strictificationPullback B).2).mp hconj
        simpa [comp, strictificationFunctor, strictificationInverse,
          strictificationProjection, StrictificationHom.base] using hheq.symm
      · intro A
        let xA : Functor.Fiber p
            (p.obj ((strictificationInverse P).obj A)) :=
          ⟨(strictificationInverse P).obj A, rfl⟩
        let wA := P.pullbackMap
          (𝟙 (p.obj ((strictificationInverse P).obj A))) xA
        let eA' := CategoryTheory.IsHomLift.domain_eq p
          (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
        let eA0 : p.obj ((strictificationInverse P).obj A) = A.V := by
          change p.obj ((strictificationPullback A).1) = A.V
          exact (strictificationPullback A).2
        letI : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
          convert h using 1 <;>
            simp [eA', strictificationObjectOf, strictificationPullback]
        dsimp [e, NatIso.ofComponents, component, comp,
          strictificationProjection, StrictificationHom.base]
        change eqToHom eA'.symm ≫ p.map wA ≫ eqToHom eA0 =
          eqToHom eA0
        rw [hwA]
        simp
  }⟩

theorem fibred_category_equivalent_to_split
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibered] :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, uS},
      IsFibredEquivalenceOver p (splitFibredProjection F) := by
  sorry

end

end Formalization.Books.Categories.Unit36
