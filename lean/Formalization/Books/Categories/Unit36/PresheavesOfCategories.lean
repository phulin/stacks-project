import Formalization.Books.Categories.Unit34.Inertia
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Skeletal

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
open Formalization.Books.Categories.Unit34

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

/-- The data needed when a pullback choice is used as the ordinary
presheaf underlying a CoGrothendieck construction.  The two last fields are
deliberately equalities of bundled functors: natural isomorphisms are not
enough for the strict split presentation used in this chapter. -/
structure StrictPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] where
  choice : PullbackChoice p
  unital : choice.IsUnital
  strict : isStrictPullbackChoice choice
  pullbackFunctor_id : ∀ (U : C),
    choice.pullbackFunctor (𝟙 U) = 𝟭 (Functor.Fiber p U)
  pullbackFunctor_comp : ∀ {W V U : C} (g : W ⟶ V) (f : V ⟶ U),
    choice.pullbackFunctor (g ≫ f) =
      choice.pullbackFunctor f ⋙ choice.pullbackFunctor g

namespace StrictPullbackChoice

variable {S C : Type*} [Category* S] [Category* C]
variable {p : S ⥤ C} [p.IsFibered]

@[simp]
theorem id_eq (Q : StrictPullbackChoice (p := p)) (U : C) :
    Q.choice.pullbackFunctor (𝟙 U) = 𝟭 (Functor.Fiber p U) :=
  Q.pullbackFunctor_id U

theorem comp_eq (Q : StrictPullbackChoice (p := p))
    {W V U : C} (g : W ⟶ V) (f : V ⟶ U) :
    Q.choice.pullbackFunctor (g ≫ f) =
      Q.choice.pullbackFunctor f ⋙ Q.choice.pullbackFunctor g :=
  Q.pullbackFunctor_comp g f

end StrictPullbackChoice

/-- Transport of a strict pullback choice along a strict isomorphism over the
base.  The inverse functor transports the chosen cartesian arrows, while the
strict triangle equations identify the resulting bundled pullback functors.
The bundled identity and composition equations are part of the result so
that callers do not have to weaken them to natural isomorphisms. -/
theorem IsomorphicOverBase.transportPullbackChoice
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {q : T ⥤ C} [q.IsFibered]
    (h : IsomorphicOverBase p q)
    (Q : StrictPullbackChoice (p := q)) :
    Nonempty (StrictPullbackChoice (p := p)) := by
  rcases h with ⟨F, G, hFq, hGp, hFG, hGF⟩
  cases hGp
  have strong_map : ∀ {R S : C} {a b : T} (f : R ⟶ S) (φ : a ⟶ b),
      (G ⋙ p).IsStronglyCartesian f φ →
        p.IsStronglyCartesian f (G.map φ) := by
    intro R₀ S₀ a b f φ hφ
    let := hφ
    refine { toIsHomLift := ?_, universal_property' := ?_ }
    · apply CategoryTheory.IsHomLift.of_fac' p f (G.map φ)
        (CategoryTheory.IsHomLift.domain_eq (G ⋙ p) f φ)
        (CategoryTheory.IsHomLift.codomain_eq (G ⋙ p) f φ)
      simpa only [Functor.comp_map] using
        (CategoryTheory.IsHomLift.fac' (G ⋙ p) f φ)
    · intro a' g τ hτ
      let := hτ
      have e_a : G.obj (F.obj a') = a' := by
        simpa only [Functor.comp_obj, Functor.id_obj] using
          congrArg (fun H : S ⥤ S => H.obj a') hFG
      have e_b : F.obj (G.obj b) = b := by
        simpa only [Functor.comp_obj, Functor.id_obj] using
          congrArg (fun H : T ⥤ T => H.obj b) hGF
      have e_bg : G.obj (F.obj (G.obj b)) = G.obj b := by
        simpa only [Functor.comp_obj, Functor.id_obj] using
          congrArg (fun H : S ⥤ S => H.obj (G.obj b)) hFG
      have hnat : G.map (F.map τ) =
          eqToHom e_a ≫ τ ≫ eqToHom e_bg.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using
          (Functor.congr_hom hFG τ)
      have hmap : G.map (F.map τ) ≫ G.map (eqToHom e_b) =
          eqToHom e_a ≫ τ := by
        rw [eqToHom_map, hnat]
        simp [Category.assoc]
      let τ' : F.obj a' ⟶ b := F.map τ ≫ eqToHom e_b
      let g' : (G ⋙ p).obj (F.obj a') ⟶ R₀ :=
        p.map (eqToHom e_a) ≫ g
      have hτ' : (G ⋙ p).IsHomLift (g' ≫ f) τ' := by
        apply CategoryTheory.IsHomLift.of_fac' (G ⋙ p) (g' ≫ f) τ' rfl
          (CategoryTheory.IsHomLift.codomain_eq (G ⋙ p) f φ)
        dsimp [τ', g']
        rw [Functor.map_comp, hmap, Functor.map_comp]
        rw [CategoryTheory.IsHomLift.fac' p (g ≫ f) τ]
        simp [Category.assoc]
      let := hτ'
      obtain ⟨χ', ⟨hχ', hχ'fac⟩, hχ'uniq⟩ :=
        Functor.IsStronglyCartesian.universal_property
          (G ⋙ p) f φ g' (g' ≫ f) rfl τ'
      let χ : a' ⟶ G.obj a := eqToHom e_a.symm ≫ G.map χ'
      have hχ : p.IsHomLift g χ := by
        have hGχ : p.IsHomLift g' (G.map χ') := by
          apply CategoryTheory.IsHomLift.of_fac' p g' (G.map χ') rfl
            (CategoryTheory.IsHomLift.codomain_eq (G ⋙ p) g' χ')
          simpa only [Functor.comp_map] using
            (CategoryTheory.IsHomLift.fac' (G ⋙ p) g' χ')
        let := hGχ
        dsimp [χ, g']
        apply CategoryTheory.IsHomLift.of_fac' p g χ rfl
          (CategoryTheory.IsHomLift.domain_eq (G ⋙ p) f φ)
        change p.map (eqToHom e_a.symm ≫ G.map χ') = _
        rw [Functor.map_comp]
        rw [CategoryTheory.IsHomLift.fac' p g' (G.map χ')]
        dsimp [g']
        simp only [Category.id_comp, Category.assoc]
        rw [← Category.assoc]
        rw [← Functor.map_comp]
        simp
      refine ⟨χ, ⟨hχ, ?_⟩, ?_⟩
      · dsimp [χ]
        rw [Category.assoc, ← G.map_comp, hχ'fac]
        dsimp [τ']
        rw [Functor.map_comp, hmap]
        simp
      · intro χ'' hχ''
        rcases hχ'' with ⟨hχ''lift, hχ''fac⟩
        have e_A : F.obj (G.obj a) = a := by
          simpa only [Functor.comp_obj, Functor.id_obj] using
            congrArg (fun H : T ⥤ T => H.obj a) hGF
        have hdom : (G ⋙ p).obj (F.obj a') = p.obj a' := by
          simpa only [Functor.comp_obj] using
            congrArg (fun H : S ⥤ C => H.obj a') hFq
        have hcod : (G ⋙ p).obj (F.obj (G.obj a)) = p.obj (G.obj a) := by
          simpa only [Functor.comp_obj] using
            congrArg (fun H : S ⥤ C => H.obj (G.obj a)) hFq
        have hq_a : (G ⋙ p).obj a = R₀ :=
          CategoryTheory.IsHomLift.domain_eq (G ⋙ p) f φ
        have hq_FGa : (G ⋙ p).obj (F.obj (G.obj a)) = R₀ :=
          (congrArg (G ⋙ p).obj e_A).trans hq_a
        have e_ga : G.obj (F.obj (G.obj a)) = G.obj a := by
          simpa only [Functor.comp_obj, Functor.id_obj] using
            congrArg (fun H : S ⥤ S => H.obj (G.obj a)) hFG
        have hFχ : (G ⋙ p).IsHomLift g' (F.map χ'') := by
          apply CategoryTheory.IsHomLift.of_fac' (G ⋙ p) g' (F.map χ'') rfl hq_FGa
          have hmapχ : (G ⋙ p).map (F.map χ'') =
              eqToHom hdom ≫ p.map χ'' ≫ eqToHom hcod.symm := by
            simpa only [Functor.comp_map, Functor.id_map] using
              (Functor.congr_hom hFq χ'')
          rw [hmapχ]
          have h := CategoryTheory.IsHomLift.fac' p g χ''
          dsimp [g']
          rw [h]
          have hdom_eq : hdom = congrArg p.obj e_a := Subsingleton.elim _ _
          have hcod_eq : hcod = congrArg p.obj e_ga := Subsingleton.elim _ _
          have hq_FGa_eq : hq_FGa = (congrArg p.obj e_ga).trans hq_a :=
            Subsingleton.elim _ _
          rw [hdom_eq, hcod_eq, hq_FGa_eq]
          rw [eqToHom_map]
          simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
            Category.id_comp]
        let : (G ⋙ p).IsHomLift (𝟙 R₀) (eqToHom e_A) :=
          CategoryTheory.IsHomLift.eqToHom_domain_lift_id e_A hq_FGa
        let χF : F.obj a' ⟶ a := F.map χ'' ≫ eqToHom e_A
        let := hFχ
        have hχF : (G ⋙ p).IsHomLift g' χF := by
          dsimp [χF]
          exact CategoryTheory.IsHomLift.comp_lift_id_right' (G ⋙ p) g'
            (F.map χ'') R₀ (eqToHom e_A)
        have hnatGF : F.map (G.map φ) =
            eqToHom e_A ≫ φ ≫ eqToHom e_b.symm := by
          simpa only [Functor.comp_map, Functor.id_map] using
            (Functor.congr_hom hGF φ)
        have hrel : eqToHom e_A ≫ φ =
            F.map (G.map φ) ≫ eqToHom e_b := by
          rw [hnatGF]
          simp [Category.assoc]
        have hχFfac : χF ≫ φ = τ' := by
          dsimp [χF, τ']
          rw [Category.assoc, hrel, ← Category.assoc, ← F.map_comp, hχ''fac]
        have heq := hχ'uniq χF ⟨hχF, hχFfac⟩
        have hmapeq := congrArg G.map heq
        have hnatFG : G.map (F.map χ'') =
            eqToHom e_a ≫ χ'' ≫ eqToHom e_ga.symm := by
          simpa only [Functor.comp_map, Functor.id_map] using
            (Functor.congr_hom hFG χ'')
        dsimp [χ, χF]
        calc
          χ'' = eqToHom e_a.symm ≫
              G.map (F.map χ'' ≫ eqToHom e_A) := by
            rw [Functor.map_comp, eqToHom_map, hnatFG]
            simp [Category.assoc]
          _ = eqToHom e_a.symm ≫ G.map χ' := by rw [hmapeq]
  let forwardFiber : ∀ {U : C}, Functor.Fiber p U →
      Functor.Fiber (G ⋙ p) U := fun {U} x =>
    ⟨F.obj x.1, by
      calc
        (G ⋙ p).obj (F.obj x.1) = p.obj x.1 := by
          simpa only [Functor.comp_obj] using
            congrArg (fun H : S ⥤ C => H.obj x.1) hFq
        _ = U := x.2⟩
  let transportedFiber : ∀ {U : C}, Functor.Fiber (G ⋙ p) U →
      Functor.Fiber p U := fun {U} x => ⟨G.obj x.1, x.2⟩
  let correction : ∀ {U : C} (x : Functor.Fiber p U),
      G.obj (F.obj x.1) = x.1 := fun {U} x => by
    simpa only [Functor.comp_obj, Functor.id_obj] using
      congrArg (fun H : S ⥤ S => H.obj x.1) hFG
  let forwardMap : ∀ {U : C} {x y : Functor.Fiber p U},
      (φ : x ⟶ y) → forwardFiber x ⟶ forwardFiber y := by
    intro U x y φ
    letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
    have hFmap : (G ⋙ p).map (F.map φ.1) =
        eqToHom (forwardFiber x).2 ≫ 𝟙 U ≫
          eqToHom (forwardFiber y).2.symm := by
      have h := Functor.congr_hom hFq φ.1
      rw [CategoryTheory.IsHomLift.fac' p (𝟙 U) φ.1] at h
      simpa [Functor.comp_map, Functor.id_map, Category.assoc] using h
    refine ⟨F.map φ.1, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac' (G ⋙ p) (𝟙 U)
      (F.map φ.1) (forwardFiber x).2 (forwardFiber y).2
    exact hFmap
  let pullback : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
      Functor.Fiber p R := fun {R S} f x =>
    transportedFiber (Q.choice.pullback f (forwardFiber x))
  let pullbackMap : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
      (Functor.Fiber.fiberInclusion.obj (pullback f x)) ⟶ x.1 := fun {R S} f x =>
    G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
      eqToHom (correction x)
  have pullbackMap_strong : ∀ {R S : C} (f : R ⟶ S) (x : Functor.Fiber p S),
      p.IsStronglyCartesian f (pullbackMap f x) := by
    intro R S f x
    let y := Q.choice.pullbackMap f (forwardFiber x)
    have hy : (G ⋙ p).IsStronglyCartesian f y :=
      Q.choice.pullbackMap_isStronglyCartesian f (forwardFiber x)
    have hGy : p.IsStronglyCartesian f (G.map y) := strong_map f y hy
    let := hGy
    have hcorr : p.IsStronglyCartesian (𝟙 S) (eqToHom (correction x)) := by
      let : p.IsHomLift (𝟙 S) (eqToHom (correction x)) :=
        CategoryTheory.IsHomLift.eqToHom_domain_lift_id (correction x)
          (forwardFiber x).2
      let : p.IsHomLift (𝟙 S) (eqToIso (correction x)).hom := by
        simpa only [eqToIso.hom] using
          (CategoryTheory.IsHomLift.eqToHom_domain_lift_id (correction x)
            (forwardFiber x).2)
      exact Functor.IsStronglyCartesian.of_iso p (𝟙 S)
        (eqToIso (correction x))
    let := hcorr
    dsimp [pullbackMap, y]
    change p.IsStronglyCartesian f
      (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
        eqToHom (correction x))
    simpa only [Category.comp_id] using
      (inferInstance : p.IsStronglyCartesian
        (f ≫ 𝟙 S)
        (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
          eqToHom (correction x)))
  let P : PullbackChoice p :=
    { pullback := pullback
      pullbackMap := pullbackMap
      pullbackMap_isStronglyCartesian := pullbackMap_strong }
  have pullbackMap_fac {R S : C} (f : R ⟶ S)
      {x y : Functor.Fiber p S} (φ : x ⟶ y) :
      ((P.pullbackFunctor f).map φ).1 ≫ P.pullbackMap f y =
        P.pullbackMap f x ≫ φ.1 := by
    let : p.IsHomLift (𝟙 S) φ.1 := φ.2
    let : p.IsStronglyCartesian f (P.pullbackMap f y) :=
      P.pullbackMap_isStronglyCartesian f y
    let : p.IsStronglyCartesian f (P.pullbackMap f x) :=
      P.pullbackMap_isStronglyCartesian f x
    have hφ' : p.IsHomLift f (P.pullbackMap f x ≫ φ.1) :=
      IsHomLift.comp_lift_id_right' p f (P.pullbackMap f x) S φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _ f
        (P.pullbackMap f y) _ _ _ (𝟙 R) f (by simp)
        (P.pullbackMap f x ≫ φ.1) hφ') ≫ P.pullbackMap f y =
        P.pullbackMap f x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac p f (P.pullbackMap f y)
      (f' := f) (g := 𝟙 R) (by simp) (P.pullbackMap f x ≫ φ.1)
  have q_pullbackMap_fac {R S : C} (f : R ⟶ S)
      {x y : Functor.Fiber (G ⋙ p) S} (φ : x ⟶ y) :
      ((Q.choice.pullbackFunctor f).map φ).1 ≫
          Q.choice.pullbackMap f y =
        Q.choice.pullbackMap f x ≫ φ.1 := by
    let : (G ⋙ p).IsHomLift (𝟙 S) φ.1 := φ.2
    let : (G ⋙ p).IsStronglyCartesian f (Q.choice.pullbackMap f y) :=
      Q.choice.pullbackMap_isStronglyCartesian f y
    let : (G ⋙ p).IsStronglyCartesian f (Q.choice.pullbackMap f x) :=
      Q.choice.pullbackMap_isStronglyCartesian f x
    have hφ' : (G ⋙ p).IsHomLift f
        (Q.choice.pullbackMap f x ≫ φ.1) :=
      IsHomLift.comp_lift_id_right' (G ⋙ p) f
        (Q.choice.pullbackMap f x) S φ.1
    change
      (@Functor.IsStronglyCartesian.map _ _ _ _ (G ⋙ p) _ _ _ _ f
        (Q.choice.pullbackMap f y) _ _ _ (𝟙 R) f (by simp)
        (Q.choice.pullbackMap f x ≫ φ.1) hφ') ≫
          Q.choice.pullbackMap f y =
        Q.choice.pullbackMap f x ≫ φ.1
    exact Functor.IsStronglyCartesian.fac (G ⋙ p) f
      (Q.choice.pullbackMap f y) (f' := f) (g := 𝟙 R) (by simp)
      (Q.choice.pullbackMap f x ≫ φ.1)
  have pullbackFunctor_map_eq {R S : C} (f : R ⟶ S)
      {x y : Functor.Fiber p S} (φ : x ⟶ y) :
      ((P.pullbackFunctor f).map φ).1 =
        G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1 := by
    have hqfac := q_pullbackMap_fac f (forwardMap φ)
    have hnat : G.map (F.map φ.1) =
        eqToHom (correction x) ≫ φ.1 ≫
          eqToHom (correction y).symm := by
      simpa only [Functor.comp_map, Functor.id_map] using
        (Functor.congr_hom hFG φ.1)
    have hright0 :
        G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1 ≫
          (G.map (Q.choice.pullbackMap f (forwardFiber y)) ≫
            eqToHom (correction y)) =
        (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
          eqToHom (correction x)) ≫ φ.1
        := by
      have hGfac := congrArg
        (fun k => G.map k ≫ eqToHom (correction y)) hqfac
      have hmap₁ := G.map_comp
        ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1
        (Q.choice.pullbackMap f (forwardFiber y))
      have hmap₂ := G.map_comp
        (Q.choice.pullbackMap f (forwardFiber x)) (forwardMap φ).1
      have hGfac' :
          (G.map ((Q.choice.pullbackFunctor f).map
              (forwardMap φ)).1 ≫
            G.map (Q.choice.pullbackMap f (forwardFiber y))) ≫
              eqToHom (correction y) =
            (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
              G.map (forwardMap φ).1) ≫ eqToHom (correction y) := by
        exact (congrArg (fun z => z ≫ eqToHom (correction y)) hmap₁).symm.trans
          (hGfac.trans
            (congrArg (fun z => z ≫ eqToHom (correction y)) hmap₂))
      have hlast :
          (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
            G.map (forwardMap φ).1) ≫ eqToHom (correction y) =
          (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
            eqToHom (correction x)) ≫ φ.1 := by
        have hnat' : G.map (forwardMap φ).1 ≫ eqToHom (correction y) =
            eqToHom (correction x) ≫ φ.1 := by
          dsimp [forwardMap]
          rw [hnat]
          simp [Category.assoc]
        calc
          _ = G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
              (G.map (forwardMap φ).1 ≫ eqToHom (correction y)) :=
            Category.assoc _ _ _
          _ = G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
              (eqToHom (correction x) ≫ φ.1) := congrArg _ hnat'
          _ = _ := (Category.assoc _ _ _).symm
      rw [← Category.assoc]
      exact hGfac'.trans hlast
    have hright :
        G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1 ≫
          P.pullbackMap f y = P.pullbackMap f x ≫ φ.1 := by
      change G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1 ≫
          (G.map (Q.choice.pullbackMap f (forwardFiber y)) ≫
            eqToHom (correction y)) =
        (G.map (Q.choice.pullbackMap f (forwardFiber x)) ≫
          eqToHom (correction x)) ≫ φ.1
      exact hright0
    have hleft := pullbackMap_fac f φ
    have hleftLift : p.IsHomLift (𝟙 R) ((P.pullbackFunctor f).map φ).1 :=
      (P.pullbackFunctor f).map φ |>.2
    have hrightLift : p.IsHomLift (𝟙 R)
        (G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1) := by
      let : (G ⋙ p).IsHomLift (𝟙 R)
          ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1 :=
        ((Q.choice.pullbackFunctor f).map (forwardMap φ)).2
      apply CategoryTheory.IsHomLift.of_fac' p (𝟙 R)
        (G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1)
        (P.pullback f x).2 (P.pullback f y).2
      simpa only [Functor.comp_map] using
        (CategoryTheory.IsHomLift.fac' (G ⋙ p) (𝟙 R)
          ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1)
    exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ f
      (P.pullbackMap f y)
      (P.pullbackMap_isStronglyCartesian f y)
      _ _ (𝟙 R) ((P.pullbackFunctor f).map φ).1
        (G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1)
      hleftLift hrightLift
      (hleft.trans hright.symm)
  have backward_forward : ∀ {U : C} (y : Functor.Fiber (G ⋙ p) U),
      forwardFiber (transportedFiber y) = y := by
    intro U y
    apply Subtype.ext
    change F.obj (G.obj y.1) = y.1
    simpa only [Functor.comp_obj, Functor.id_obj] using
      congrArg (fun H : T ⥤ T => H.obj y.1) hGF
  have hcomp : ∀ {W V U : C} (g : W ⟶ V) (f : V ⟶ U),
      P.pullbackFunctor (g ≫ f) = P.pullbackFunctor f ⋙ P.pullbackFunctor g := by
    let forwardFunctor (U : C) :
        Functor.Fiber p U ⥤ Functor.Fiber (G ⋙ p) U :=
      { obj := forwardFiber
        map := forwardMap
        map_id := by
          intro x
          apply Functor.Fiber.hom_ext
          change F.map (𝟙 x.1) = 𝟙 (F.obj x.1)
          simp
        map_comp := by
          intro x y z φ ψ
          apply Functor.Fiber.hom_ext
          change F.map (φ.1 ≫ ψ.1) = F.map φ.1 ≫ F.map ψ.1
          simp }
    let transportedMap : ∀ {U : C}
        {x y : Functor.Fiber (G ⋙ p) U}, (x ⟶ y) →
          (transportedFiber x ⟶ transportedFiber y) := by
      intro U x y φ
      let : (G ⋙ p).IsHomLift (𝟙 U) φ.1 := φ.2
      refine ⟨G.map φ.1, ?_⟩
      apply CategoryTheory.IsHomLift.of_fac' p (𝟙 U) (G.map φ.1)
        x.2 y.2
      simpa only [Functor.comp_map] using
        (CategoryTheory.IsHomLift.fac' (G ⋙ p) (𝟙 U) φ.1)
    let transportedFunctor (U : C) :
        Functor.Fiber (G ⋙ p) U ⥤ Functor.Fiber p U :=
      { obj := transportedFiber
        map := transportedMap
        map_id := by
          intro x
          apply Functor.Fiber.hom_ext
          change G.map (𝟙 x.1) = 𝟙 (G.obj x.1)
          simp
        map_comp := by
          intro x y z φ ψ
          apply Functor.Fiber.hom_ext
          change G.map (φ.1 ≫ ψ.1) = G.map φ.1 ≫ G.map ψ.1
          simp }
    have transported_forward (U : C) :
        transportedFunctor U ⋙ forwardFunctor U =
          𝟭 (Functor.Fiber (G ⋙ p) U) := by
      refine CategoryTheory.Functor.ext
        (fun y => by
          change forwardFiber (transportedFiber y) = y
          exact backward_forward y) (fun x y φ => ?_)
      apply Functor.Fiber.hom_ext
      let dX := Functor.congr_obj hGF x.1
      let dY := Functor.congr_obj hGF y.1
      have hmapX :
          Functor.Fiber.fiberInclusion.map
              (eqToHom (backward_forward x)) = eqToHom dX := by
        have h := eqToHom_map
          (Functor.Fiber.fiberInclusion :
            Functor.Fiber (G ⋙ p) U ⥤ T) (backward_forward x)
        have he :
            congrArg (fun z : Functor.Fiber (G ⋙ p) U => z.1)
                (backward_forward x) = dX := by
          apply Subsingleton.elim
        exact h.trans (congrArg (fun e => eqToHom e) he)
      have hmapY :
          Functor.Fiber.fiberInclusion.map
              (eqToHom (backward_forward y).symm) = eqToHom dY.symm := by
        have h := eqToHom_map
          (Functor.Fiber.fiberInclusion :
            Functor.Fiber (G ⋙ p) U ⥤ T) (backward_forward y).symm
        have he₀ :
            congrArg (fun z : Functor.Fiber (G ⋙ p) U => z.1)
                (backward_forward y) = dY := by
          apply Subsingleton.elim
        have he :
            congrArg (fun z : Functor.Fiber (G ⋙ p) U => z.1)
                (backward_forward y).symm = dY.symm :=
          congrArg (fun e => e.symm) he₀
        exact h.trans (congrArg (fun e => eqToHom e) he)
      change F.map (G.map φ.1) =
        Functor.Fiber.fiberInclusion.map
            (eqToHom (backward_forward x)) ≫ φ.1 ≫
          Functor.Fiber.fiberInclusion.map
            (eqToHom (backward_forward y).symm)
      rw [hmapX, hmapY]
      change F.map (G.map φ.1) =
        eqToHom (Functor.congr_obj hGF x.1) ≫ φ.1 ≫
          eqToHom (Functor.congr_obj hGF y.1).symm
      simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.id_map] using (Functor.congr_hom hGF φ.1)
    have forward_transported (U : C) :
        forwardFunctor U ⋙ transportedFunctor U =
          𝟭 (Functor.Fiber p U) := by
      have hobj : ∀ x : Functor.Fiber p U,
          (forwardFunctor U ⋙ transportedFunctor U).obj x =
            (𝟭 (Functor.Fiber p U)).obj x := by
        intro x
        apply Subtype.ext
        exact correction x
      refine CategoryTheory.Functor.ext hobj (fun x y φ => ?_)
      apply Functor.Fiber.hom_ext
      let dX := congrArg
        (fun z : Functor.Fiber p U =>
          (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S).obj z)
        (hobj x)
      let dY := congrArg
        (fun z : Functor.Fiber p U =>
          (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S).obj z)
        (hobj y)
      have hmapX :
          Functor.Fiber.fiberInclusion.map (eqToHom (hobj x)) =
            eqToHom (correction x) := by
        have h := eqToHom_map
          (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S) (hobj x)
        have he : dX = correction x := by
          apply Subsingleton.elim
        exact h.trans (congrArg (fun e => eqToHom e) he)
      have hmapY :
          Functor.Fiber.fiberInclusion.map (eqToHom (hobj y).symm) =
            eqToHom (correction y).symm := by
        have h := eqToHom_map
          (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S)
            (hobj y).symm
        have he : dY.symm = (correction y).symm := by
          apply Subsingleton.elim
        exact h.trans (congrArg (fun e => eqToHom e) he)
      change G.map (F.map φ.1) =
        Functor.Fiber.fiberInclusion.map (eqToHom (hobj x)) ≫ φ.1 ≫
          Functor.Fiber.fiberInclusion.map (eqToHom (hobj y).symm)
      rw [hmapX, hmapY]
      have hFGstep := Functor.congr_hom hFG φ.1
      have heX : Functor.congr_obj hFG x.1 = correction x := by
        apply Subsingleton.elim
      have heY : Functor.congr_obj hFG y.1 = correction y := by
        apply Subsingleton.elim
      rw [heX, heY] at hFGstep
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.id_map] at hFGstep
      rw [hFGstep]
      congr 1
    have factorization {R V : C} (f : R ⟶ V) :
        P.pullbackFunctor f =
          forwardFunctor V ⋙ Q.choice.pullbackFunctor f ⋙
            transportedFunctor R := by
      let hobj : ∀ x : Functor.Fiber p V,
          (P.pullbackFunctor f).obj x =
            (forwardFunctor V ⋙ Q.choice.pullbackFunctor f ⋙
              transportedFunctor R).obj x := by
        intro x
        change transportedFiber (Q.choice.pullback f (forwardFiber x)) =
          transportedFiber (Q.choice.pullback f (forwardFiber x))
        rfl
      cases hL : P.pullbackFunctor f with
      | mk Lobj Lmap Lid Lcomp =>
        cases hR : forwardFunctor V ⋙ Q.choice.pullbackFunctor f ⋙
            transportedFunctor R with
        | mk Robj Rmap Rid Rcomp =>
          cases hL
          cases hR
          congr
          funext x y φ
          apply Functor.Fiber.hom_ext
          dsimp [Functor.Fiber.fiberInclusion]
          change ((P.pullbackFunctor f).map φ).1 =
            G.map ((Q.choice.pullbackFunctor f).map (forwardMap φ)).1
          exact pullbackFunctor_map_eq f φ
    intro W V U g f
    calc
      P.pullbackFunctor (g ≫ f) =
          forwardFunctor U ⋙ Q.choice.pullbackFunctor (g ≫ f) ⋙
            transportedFunctor W := factorization (g ≫ f)
      _ = forwardFunctor U ⋙
          (Q.choice.pullbackFunctor f ⋙ Q.choice.pullbackFunctor g) ⋙
            transportedFunctor W := by rw [Q.comp_eq g f]
      _ = (forwardFunctor U ⋙ Q.choice.pullbackFunctor f ⋙
          transportedFunctor V) ⋙
          (forwardFunctor V ⋙ Q.choice.pullbackFunctor g ⋙
            transportedFunctor W) := by
        have hcancel := congrArg
          (fun K : Functor.Fiber (G ⋙ p) V ⥤
              Functor.Fiber (G ⋙ p) V =>
            forwardFunctor U ⋙ Q.choice.pullbackFunctor f ⋙ K ⋙
              Q.choice.pullbackFunctor g ⋙ transportedFunctor W)
          (transported_forward V)
        simpa only [Functor.assoc, Functor.id_comp] using hcancel.symm
      _ = P.pullbackFunctor f ⋙ P.pullbackFunctor g := by
        rw [factorization f, factorization g]
  refine ⟨{
    choice := P
    unital := ?_
    strict := ?_
    pullbackFunctor_id := ?_
    pullbackFunctor_comp := ?_ }⟩
  · intro U x
    apply Subtype.ext
    change G.obj (Q.choice.pullback (𝟙 U) (forwardFiber x)).1 = x.1
    rw [Q.unital U (forwardFiber x)]
    exact correction x
  · intro W V U g f
    exact hcomp g f
  · intro U
    have hobj : ∀ x : Functor.Fiber p U,
        (P.pullbackFunctor (𝟙 U)).obj x = (𝟭 (Functor.Fiber p U)).obj x := by
      intro x
      apply Subtype.ext
      change G.obj (Q.choice.pullback (𝟙 U) (forwardFiber x)).1 = x.1
      rw [Q.unital U (forwardFiber x)]
      exact correction x
    refine CategoryTheory.Functor.ext (fun x => hobj x) (fun x y φ => ?_)
    apply Functor.Fiber.hom_ext
    dsimp [Functor.Fiber.fiberInclusion]
    change ((P.pullbackFunctor (𝟙 U)).map φ).1 =
      (eqToHom (hobj x) ≫
        (𝟭 (Functor.Fiber p U)).map φ ≫ eqToHom (hobj y).symm).1
    rw [pullbackFunctor_map_eq (𝟙 U) φ]
    have hQid := Functor.congr_hom (Q.id_eq U) (forwardMap φ)
    have hQid' := congrArg (fun m => m.1) hQid
    change ((Q.choice.pullbackFunctor (𝟙 U)).map (forwardMap φ)).1 =
      Functor.Fiber.fiberInclusion.map
          (eqToHom (Functor.congr_obj (Q.id_eq U) (forwardFiber x))) ≫
        (forwardMap φ).1 ≫
          Functor.Fiber.fiberInclusion.map
            (eqToHom (Functor.congr_obj (Q.id_eq U) (forwardFiber y)).symm) at hQid'
    let dX := congrArg (fun z : Functor.Fiber (G ⋙ p) U => z.1)
      (Functor.congr_obj (Q.id_eq U) (forwardFiber x))
    let dY := congrArg (fun z : Functor.Fiber (G ⋙ p) U => z.1)
      (Functor.congr_obj (Q.id_eq U) (forwardFiber y))
    have hmapXq :
        Functor.Fiber.fiberInclusion.map
            (eqToHom (Functor.congr_obj (Q.id_eq U) (forwardFiber x))) =
          eqToHom dX := by
      dsimp [dX]
      exact eqToHom_map
        (Functor.Fiber.fiberInclusion : Functor.Fiber (G ⋙ p) U ⥤ T)
        (Functor.congr_obj (Q.id_eq U) (forwardFiber x))
    have hmapYq :
        Functor.Fiber.fiberInclusion.map
            (eqToHom (Functor.congr_obj (Q.id_eq U) (forwardFiber y)).symm) =
          eqToHom dY.symm := by
      dsimp [dY]
      exact eqToHom_map
        (Functor.Fiber.fiberInclusion : Functor.Fiber (G ⋙ p) U ⥤ T)
        (Functor.congr_obj (Q.id_eq U) (forwardFiber y)).symm
    rw [hmapXq, hmapYq] at hQid'
    have hGQid := congrArg G.map hQid'
    have hGQid' :
        G.map ((Q.choice.pullbackFunctor (𝟙 U)).map (forwardMap φ)).1 =
          G.map (eqToHom dX) ≫ G.map (forwardMap φ).1 ≫
            G.map (eqToHom dY.symm) := by
      calc
        _ = G.map (eqToHom dX ≫ (forwardMap φ).1 ≫ eqToHom dY.symm) := hGQid
        _ = _ := by simp only [Functor.map_comp]
    have hGQid'' :
        G.map ((Q.choice.pullbackFunctor (𝟙 U)).map (forwardMap φ)).1 =
          eqToHom (congrArg G.obj dX) ≫ G.map (forwardMap φ).1 ≫
            eqToHom (congrArg G.obj dY).symm := by
      calc
        _ = G.map (eqToHom dX) ≫ G.map (forwardMap φ).1 ≫
            G.map (eqToHom dY.symm) := hGQid'
        _ = _ := by rw [eqToHom_map, eqToHom_map]
    have hnat : G.map (F.map φ.1) =
        eqToHom (correction x) ≫ φ.1 ≫
          eqToHom (correction y).symm := by
      have hFGstep := Functor.congr_hom hFG φ.1
      have heX : Functor.congr_obj hFG x.1 = correction x := by
        apply Subsingleton.elim
      have heY : Functor.congr_obj hFG y.1 = correction y := by
        apply Subsingleton.elim
      rw [heX, heY] at hFGstep
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.id_map] at hFGstep
      exact hFGstep
    have hobjX :
        congrArg (fun z : Functor.Fiber p U => z.1) (hobj x) =
          (congrArg G.obj dX).trans (correction x) := by
      apply Subsingleton.elim
    have hobjY :
        congrArg (fun z : Functor.Fiber p U => z.1) (hobj y) =
          (congrArg G.obj dY).trans (correction y) := by
      apply Subsingleton.elim
    have hmapHX :
        Functor.Fiber.fiberInclusion.map (eqToHom (hobj x)) =
          eqToHom (congrArg (fun z : Functor.Fiber p U => z.1) (hobj x)) := by
      exact eqToHom_map
        (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S) (hobj x)
    have hmapHY :
        Functor.Fiber.fiberInclusion.map (eqToHom (hobj y).symm) =
          eqToHom (congrArg (fun z : Functor.Fiber p U => z.1) (hobj y)).symm := by
      have h := eqToHom_map
        (Functor.Fiber.fiberInclusion : Functor.Fiber p U ⥤ S) (hobj y).symm
      have he :
          congrArg (fun z : Functor.Fiber p U => z.1) (hobj y).symm =
            (congrArg (fun z : Functor.Fiber p U => z.1) (hobj y)).symm :=
        Subsingleton.elim _ _
      exact h.trans (congrArg (fun e => eqToHom e) he)
    have hright :
        (eqToHom (hobj x) ≫
            (𝟭 (Functor.Fiber p U)).map φ ≫ eqToHom (hobj y).symm).1 =
          eqToHom ((congrArg G.obj dX).trans (correction x)) ≫ φ.1 ≫
            eqToHom ((congrArg G.obj dY).trans (correction y)).symm := by
      change Functor.Fiber.fiberInclusion.map (eqToHom (hobj x)) ≫ φ.1 ≫
          Functor.Fiber.fiberInclusion.map (eqToHom (hobj y).symm) = _
      rw [hmapHX, hmapHY, hobjX, hobjY]
      congr 1
    have hfinal :
        (eqToHom (congrArg G.obj dX) ≫
            (eqToHom (correction x) ≫ φ.1 ≫ eqToHom (correction y).symm) ≫
              eqToHom (congrArg G.obj dY).symm) =
          eqToHom ((congrArg G.obj dX).trans (correction x)) ≫ φ.1 ≫
            eqToHom ((congrArg G.obj dY).trans (correction y)).symm := by
      calc
        _ = (eqToHom (congrArg G.obj dX) ≫ eqToHom (correction x)) ≫ φ.1 ≫
            (eqToHom (correction y).symm ≫ eqToHom (congrArg G.obj dY).symm) := by
          simp only [Category.assoc]
        _ = eqToHom ((congrArg G.obj dX).trans (correction x)) ≫ φ.1 ≫
            eqToHom ((correction y).symm.trans (congrArg G.obj dY).symm) := by
          rw [eqToHom_trans, eqToHom_trans]
        _ = _ := by
          have he :
              (correction y).symm.trans (congrArg G.obj dY).symm =
                ((congrArg G.obj dY).trans (correction y)).symm :=
            Subsingleton.elim _ _
          rw [he]
    rw [hGQid'', show (forwardMap φ).1 = F.map φ.1 by rfl, hnat, hfinal,
      hright]
  · intro W V U g f
    exact hcomp g f

theorem isSplitFibredCategory_iff_exists_strictPullbackChoice
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibered] :
      IsSplitFibredCategory.{vC, uC, vS, uS, vS, uS} p ↔
      ∃ P : PullbackChoice p, P.IsUnital ∧ isStrictPullbackChoice P := by
  /- Proof plan: transport the canonical strict choice from a split
  presentation in one direction; in the other, form the fibre presheaf from
  the strict pullback functors and construct its Grothendieck equivalence. -/
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

/-- The strictification category is presented by the ordinary presheaf whose
fibre over `V` is the category of strictification objects with first base
object `V`.  Its restriction along `g : W ⟶ V` is the reindexing operation
`(x, f) ↦ (x, g ≫ f)`; the morphism component is the unique strongly
cartesian comparison supplied by `P`.  The resulting CoGrothendieck
projection is strictly isomorphic over `C` to `strictificationProjection`.

This is kept as a separate interface so the splitness theorem records the
actual CoGrothendieck presentation, rather than only an abstract existence
of a split object. -/
private def strictificationReindexHom
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W : C} (A : StrictificationObject p P) (g : W ⟶ A.V) :
    StrictificationHom P
      (A := strictificationReindexObject A g) (B := A) where
  hom := by
    let : p.IsStronglyCartesian A.f (P.pullbackMap A.f A.x) :=
      P.pullbackMap_isStronglyCartesian A.f A.x
    exact @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      A.f (P.pullbackMap A.f A.x)
      (P.pullbackMap_isStronglyCartesian A.f A.x)
      _ _ g (g ≫ A.f) rfl (P.pullbackMap (g ≫ A.f) A.x)
      (P.pullbackMap_isStronglyCartesian (g ≫ A.f) A.x).toIsHomLift

private theorem strictificationReindexHom_isStronglyCartesian
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {R : C} (B : StrictificationObject p P) (f : R ⟶ B.V) :
    (strictificationProjection P).IsStronglyCartesian f
      (strictificationReindexHom B f) := by
  let A := strictificationReindexObject B f
  let hBStrong : p.IsStronglyCartesian B.f (P.pullbackMap B.f B.x) :=
    P.pullbackMap_isStronglyCartesian B.f B.x
  let : p.IsStronglyCartesian (f ≫ B.f)
      (P.pullbackMap (f ≫ B.f) B.x) :=
    P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x
  let : p.IsHomLift (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x) := by
    exact @Functor.IsStronglyCartesian.toIsHomLift _ _ _ _ p _ _ _ _
      (f ≫ B.f) (P.pullbackMap (f ≫ B.f) B.x)
      (P.pullbackMap_isStronglyCartesian (f ≫ B.f) B.x)
  let φ : (strictificationPullback A).1 ⟶
      (strictificationPullback B).1 :=
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
    letI : (strictificationProjection P).IsHomLift (g ≫ f) τ := hτ
    have hτmap : g ≫ f = (strictificationProjection P).map τ :=
      @CategoryTheory.IsHomLift.eq_of_isHomLift C
        (StrictificationCategory p P) _ _
        (strictificationProjection P) X B (g ≫ f) τ hτ
    have hτmap' : g ≫ f =
        eqToHom eX.symm ≫ p.map τ.hom ≫ eqToHom eB := by
      simpa [strictificationProjection, StrictificationHom.base] using hτmap
    let g₀ : p.obj ((strictificationPullback X).1) ⟶ _ :=
      eqToHom eX ≫ g
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
      convert hcancel' using 1 <;> simp [Category.assoc]
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
      have hEq : c = eA := by apply Subsingleton.elim
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
  exact hκstrong

private noncomputable def strictificationPullbackChoice
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    [h : (strictificationProjection P).IsFibered] :
  PullbackChoice (strictificationProjection P) where
  pullback := by
    intro R V f x
    rcases x with ⟨A, hA⟩
    change A.V = V at hA
    subst V
    exact ⟨strictificationReindexObject A f, rfl⟩
  pullbackMap := by
    intro R V f x
    rcases x with ⟨A, hA⟩
    change A.V = V at hA
    subst V
    exact strictificationReindexHom A f
  pullbackMap_isStronglyCartesian := by
    intro R V f x
    rcases x with ⟨A, hA⟩
    change A.V = V at hA
    subst V
    exact strictificationReindexHom_isStronglyCartesian A f

private theorem strictificationPullbackChoice_isUnital
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    [h : (strictificationProjection P).IsFibered] :
    (strictificationPullbackChoice P).IsUnital := by
  intro U x
  apply Subtype.ext
  rcases x with ⟨A, hA⟩
  change A.V = U at hA
  subst U
  cases A
  change strictificationReindexObject
      ({ V := _ , U := _, f := _, x := _ } : StrictificationObject p P)
      (𝟙 _) = _
  simp [strictificationReindexObject]

private def strictificationUnderlyingFunctor
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    StrictificationCategory p P ⥤ S where
  obj A := (strictificationPullback A).1
  map φ := φ.hom
  map_id _ := rfl
  map_comp _ _ := by rfl

private theorem strictificationReindexHom_comp
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] {P : PullbackChoice p}
    {W V : C} (A : StrictificationObject p P)
    (g : W ⟶ V) (f : V ⟶ A.V) :
    eqToHom (strictificationReindexObject_comp g A f).symm ≫
        strictificationReindexHom (strictificationReindexObject A f) g ≫
          strictificationReindexHom A f =
      strictificationReindexHom A (g ≫ f) := by
  apply StrictificationHom.ext
  cases A with
  | mk V₀ U₀ f₀ x₀ =>
    have hsrc : p.obj
        (strictificationPullback
          (strictificationReindexObject
            ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
            (g ≫ f))).1 = W := by
      exact (strictificationPullback
        (strictificationReindexObject
          ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
          (g ≫ f))).2
    have htgt : p.obj
        (strictificationPullback
          (strictificationReindexObject
            (strictificationReindexObject
              ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
              f) g)).1 = W := by
      exact (strictificationPullback
        (strictificationReindexObject
          (strictificationReindexObject
            ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
            f) g)).2
    have htype :
        (strictificationPullback
          (strictificationReindexObject
            ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
            (g ≫ f))).1 ⟶
          (strictificationPullback
            (strictificationReindexObject
              (strictificationReindexObject
                ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
                f) g)).1 :=
      (eqToHom (strictificationReindexObject_comp g
        ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
        f).symm).hom
    have hEqLift : p.IsHomLift (𝟙 W)
        (eqToHom (strictificationReindexObject_comp g
          ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
          f).symm).hom := by
      apply CategoryTheory.IsHomLift.of_fac p (𝟙 W)
        (eqToHom (strictificationReindexObject_comp g
          ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
          f).symm).hom
        hsrc htgt
      have hmap :
          (strictificationProjection P).map
              (eqToHom (strictificationReindexObject_comp g
                ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
                f).symm) =
            𝟙 W := by
        rw [eqToHom_map]
        apply congrArg (fun e : W = W => eqToHom e)
        rfl
      simpa [strictificationProjection, StrictificationHom.base,
        strictificationReindexObject] using hmap.symm
    simp [strictificationReindexHom, strictificationReindexObject_comp,
      strictificationReindexObject, Category.assoc]
    let : p.IsHomLift (𝟙 W)
        (eqToHom (strictificationReindexObject_comp g
          ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
          f).symm).hom :=
      hEqLift
    let : p.IsHomLift g
        (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
          (f ≫ f₀) (P.pullbackMap (f ≫ f₀) x₀)
          (P.pullbackMap_isStronglyCartesian (f ≫ f₀) x₀)
          _ _ g (g ≫ (f ≫ f₀)) rfl
          (P.pullbackMap (g ≫ (f ≫ f₀)) x₀)
          (P.pullbackMap_isStronglyCartesian
            (g ≫ (f ≫ f₀)) x₀).toIsHomLift) := by
      exact Functor.IsStronglyCartesian.map_isHomLift p (f ≫ f₀)
        (P.pullbackMap (f ≫ f₀) x₀)
        (f' := g ≫ (f ≫ f₀)) (g := g) rfl
        (P.pullbackMap (g ≫ (f ≫ f₀)) x₀)
    let : p.IsHomLift f
        (@Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
          f₀ (P.pullbackMap f₀ x₀)
          (P.pullbackMap_isStronglyCartesian f₀ x₀)
          _ _ f (f ≫ f₀) rfl
          (P.pullbackMap (f ≫ f₀) x₀)
          (P.pullbackMap_isStronglyCartesian
            (f ≫ f₀) x₀).toIsHomLift) := by
      exact Functor.IsStronglyCartesian.map_isHomLift p f₀
        (P.pullbackMap f₀ x₀) (f' := f ≫ f₀) (g := f) rfl
        (P.pullbackMap (f ≫ f₀) x₀)
    let : p.IsStronglyCartesian f₀ (P.pullbackMap f₀ x₀) :=
      P.pullbackMap_isStronglyCartesian f₀ x₀
    let : p.IsHomLift ((g ≫ f) ≫ f₀)
        (P.pullbackMap ((g ≫ f) ≫ f₀) x₀) := by
      exact (P.pullbackMap_isStronglyCartesian ((g ≫ f) ≫ f₀) x₀).toIsHomLift
    let e₀ :=
      (eqToHom (strictificationReindexObject_comp g
        ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
        f).symm).hom
    let m₁ := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      (f ≫ f₀) (P.pullbackMap (f ≫ f₀) x₀)
      (P.pullbackMap_isStronglyCartesian (f ≫ f₀) x₀)
      _ _ g (g ≫ (f ≫ f₀)) rfl
      (P.pullbackMap (g ≫ (f ≫ f₀)) x₀)
      (P.pullbackMap_isStronglyCartesian
        (g ≫ (f ≫ f₀)) x₀).toIsHomLift
    let m₂ := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
      f₀ (P.pullbackMap f₀ x₀)
      (P.pullbackMap_isStronglyCartesian f₀ x₀)
      _ _ f (f ≫ f₀) rfl
      (P.pullbackMap (f ≫ f₀) x₀)
      (P.pullbackMap_isStronglyCartesian
        (f ≫ f₀) x₀).toIsHomLift
    letI : p.IsHomLift g m₁ := by
      dsimp [m₁]
      exact Functor.IsStronglyCartesian.map_isHomLift p (f ≫ f₀)
        (P.pullbackMap (f ≫ f₀) x₀)
        (f' := g ≫ (f ≫ f₀)) (g := g) rfl
        (P.pullbackMap (g ≫ (f ≫ f₀)) x₀)
    letI : p.IsHomLift f m₂ := by
      dsimp [m₂]
      exact Functor.IsStronglyCartesian.map_isHomLift p f₀
        (P.pullbackMap f₀ x₀) (f' := f ≫ f₀) (g := f) rfl
        (P.pullbackMap (f ≫ f₀) x₀)
    letI : p.IsHomLift (𝟙 W) e₀ := by
      dsimp [e₀]
      exact hEqLift
    have pullbackMap_eq_of_eq :
        ∀ {R S : C} (q₁ q₂ : R ⟶ S) (z : Functor.Fiber p S)
          (hq : q₁ = q₂),
          P.pullbackMap q₁ z =
            eqToHom (congrArg
              (fun q => Functor.Fiber.fiberInclusion.obj (P.pullback q z)) hq) ≫
              P.pullbackMap q₂ z := by
      intro R S q₁ q₂ z hq
      cases hq
      simp
    refine @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      f₀ (P.pullbackMap f₀ x₀)
      (P.pullbackMap_isStronglyCartesian f₀ x₀) _ _ (g ≫ f) _ _ ?_ ?_ ?_
    · change p.IsHomLift (g ≫ f) (e₀ ≫ m₁ ≫ m₂)
      have h₁₂ : p.IsHomLift (g ≫ f) (m₁ ≫ m₂) := by
        exact IsHomLift.comp p g f m₁ m₂
      letI h₁₂inst : p.IsHomLift (g ≫ f) (m₁ ≫ m₂) := h₁₂
      have hall : p.IsHomLift (𝟙 W ≫ (g ≫ f))
          (e₀ ≫ (m₁ ≫ m₂)) := by
        exact @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _
          (𝟙 W) (g ≫ f) e₀ (m₁ ≫ m₂)
          (by dsimp [e₀]; exact hEqLift) h₁₂
      simpa [Category.assoc] using hall
    · exact Functor.IsStronglyCartesian.map_isHomLift p f₀
        (P.pullbackMap f₀ x₀)
        (f' := (g ≫ f) ≫ f₀) (g := g ≫ f) (by simp)
        (P.pullbackMap ((g ≫ f) ≫ f₀) x₀)
    · have houter : m₂ ≫ P.pullbackMap f₀ x₀ =
          P.pullbackMap (f ≫ f₀) x₀ := by
        dsimp [m₂]
        exact Functor.IsStronglyCartesian.fac p f₀
          (P.pullbackMap f₀ x₀) (f' := f ≫ f₀) (g := f) rfl
          (P.pullbackMap (f ≫ f₀) x₀)
      have hinner : m₁ ≫ P.pullbackMap (f ≫ f₀) x₀ =
          P.pullbackMap (g ≫ (f ≫ f₀)) x₀ := by
        dsimp [m₁]
        exact Functor.IsStronglyCartesian.fac p (f ≫ f₀)
          (P.pullbackMap (f ≫ f₀) x₀)
          (f' := g ≫ (f ≫ f₀)) (g := g) rfl
          (P.pullbackMap (g ≫ (f ≫ f₀)) x₀)
      have htransport : e₀ ≫ P.pullbackMap (g ≫ (f ≫ f₀)) x₀ =
          P.pullbackMap ((g ≫ f) ≫ f₀) x₀ := by
        have hq : (g ≫ f) ≫ f₀ = g ≫ (f ≫ f₀) := Category.assoc _ _ _
        have he₀ : e₀ = eqToHom (congrArg
            (fun q => Functor.Fiber.fiberInclusion.obj (P.pullback q x₀)) hq) := by
          have h := eqToHom_map (strictificationUnderlyingFunctor P)
            (strictificationReindexObject_comp g
              ({ V := V₀, U := U₀, f := f₀, x := x₀ } : StrictificationObject p P)
              f).symm
          dsimp [e₀, strictificationUnderlyingFunctor] at h ⊢
          exact h
        have hpb := pullbackMap_eq_of_eq ((g ≫ f) ≫ f₀)
          (g ≫ (f ≫ f₀)) x₀ hq
        rw [he₀]
        exact hpb.symm
      let m₃ := @Functor.IsStronglyCartesian.map _ _ _ _ p _ _ _ _
            f₀ (P.pullbackMap f₀ x₀)
            (P.pullbackMap_isStronglyCartesian f₀ x₀)
            _ _ (g ≫ f) ((g ≫ f) ≫ f₀) rfl
            (P.pullbackMap ((g ≫ f) ≫ f₀) x₀)
            (P.pullbackMap_isStronglyCartesian
              ((g ≫ f) ≫ f₀) x₀).toIsHomLift
      have hdirect : m₃ ≫ P.pullbackMap f₀ x₀ =
            P.pullbackMap ((g ≫ f) ≫ f₀) x₀ := by
        dsimp [m₃]
        exact Functor.IsStronglyCartesian.fac p f₀
          (P.pullbackMap f₀ x₀)
          (f' := (g ≫ f) ≫ f₀) (g := g ≫ f) rfl
          (P.pullbackMap ((g ≫ f) ≫ f₀) x₀)
      change (e₀ ≫ m₁ ≫ m₂) ≫ P.pullbackMap f₀ x₀ =
        m₃ ≫ P.pullbackMap f₀ x₀
      have h1 : (e₀ ≫ m₁ ≫ m₂) ≫ P.pullbackMap f₀ x₀ =
          e₀ ≫ (m₁ ≫ (m₂ ≫ P.pullbackMap f₀ x₀)) := by
        exact (Category.assoc e₀ (m₁ ≫ m₂)
            (P.pullbackMap f₀ x₀)).trans
          (congrArg (fun k => e₀ ≫ k)
            (Category.assoc m₁ m₂ (P.pullbackMap f₀ x₀)))
      have h2 : e₀ ≫ (m₁ ≫ (m₂ ≫ P.pullbackMap f₀ x₀)) =
          e₀ ≫ (m₁ ≫ P.pullbackMap (f ≫ f₀) x₀) :=
        congrArg (fun k => e₀ ≫ (m₁ ≫ k)) houter
      have h3 : e₀ ≫ (m₁ ≫ P.pullbackMap (f ≫ f₀) x₀) =
          e₀ ≫ P.pullbackMap (g ≫ (f ≫ f₀)) x₀ :=
        congrArg (fun k => e₀ ≫ k) hinner
      exact h1.trans (h2.trans (h3.trans (htransport.trans hdirect.symm)))

private theorem strictificationPullbackChoice_isStrict
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p)
    [h : (strictificationProjection P).IsFibered] :
    isStrictPullbackChoice (strictificationPullbackChoice P) := by
  intro W V U g f
  let Q := strictificationPullbackChoice P
  have hobj : ∀ (x : Functor.Fiber (strictificationProjection P) U),
      Q.pullback (g ≫ f) x =
        ((Q.pullbackFunctor f ⋙ Q.pullbackFunctor g).obj x) := by
    intro x
    apply Subtype.ext
    rcases x with ⟨A, rfl⟩
    exact (strictificationReindexObject_comp g A f).symm
  have hpb {R : C} (A : StrictificationObject p P) (k : R ⟶ A.V) :
      Q.pullback k ⟨A, rfl⟩ =
        (⟨strictificationReindexObject A k, rfl⟩ :
          Functor.Fiber (strictificationProjection P) R) := by
    apply Subtype.ext
    change strictificationReindexObject A k = strictificationReindexObject A k
    rfl
  have qmap {R : C} (A : StrictificationObject p P) (k : R ⟶ A.V)
      (hp : Q.pullback k ⟨A, rfl⟩ =
        (⟨strictificationReindexObject A k, rfl⟩ :
          Functor.Fiber (strictificationProjection P) R)) :
      Q.pullbackMap k ⟨A, rfl⟩ =
          Functor.Fiber.fiberInclusion.map (eqToHom hp) ≫
          strictificationReindexHom A k := by
    have hmap := eqToHom_map
      (Functor.Fiber.fiberInclusion :
        Functor.Fiber (strictificationProjection P) R ⥤
          StrictificationCategory p P) hp
    rw [hmap]
    cases hp
    cases A
    apply StrictificationHom.ext
    simp [Q, strictificationPullbackChoice, strictificationReindexHom,
      strictificationReindexObject]
  have component_fac (x : Functor.Fiber (strictificationProjection P) U) :
      Functor.Fiber.fiberInclusion.map (eqToHom (hobj x)) ≫
          Q.pullbackMap g (Q.pullback f x) ≫ Q.pullbackMap f x =
        Q.pullbackMap (g ≫ f) x := by
    rcases x with ⟨A, hA⟩
    change A.V = U at hA
    subst U
    rw [hpb A f]
    rw [qmap (strictificationReindexObject A f) g
          (hpb (strictificationReindexObject A f) g),
      qmap A f (hpb A f), qmap A (g ≫ f) (hpb A (g ≫ f))]
    simp only [Q, strictificationPullbackChoice]
    change eqToHom (strictificationReindexObject_comp g A f).symm ≫
        strictificationReindexHom (strictificationReindexObject A f) g ≫
          strictificationReindexHom A f =
      strictificationReindexHom A (g ≫ f)
    exact strictificationReindexHom_comp A g f
  exact CategoryTheory.Functor.ext (fun x => hobj x) (by
    intro x y φ
    apply Functor.Fiber.hom_ext
    rfl)

theorem strictificationProjection_coGrothendieck_presentation
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, max (max uC vC) uS},
      IsomorphicOverBase (strictificationProjection P)
        (splitFibredProjection F) := by
  let : (strictificationProjection P).IsFibered :=
    strictificationProjection_isFibered P
  let Q := strictificationPullbackChoice P
  have hQunital : Q.IsUnital :=
    strictificationPullbackChoice_isUnital P
  have hQstrict : isStrictPullbackChoice Q :=
    strictificationPullbackChoice_isStrict P
  exact ((isSplitFibredCategory_iff_exists_strictPullbackChoice
    (strictificationProjection P)).2 ⟨Q, hQunital, hQstrict⟩).2

theorem strictificationProjection_isSplit
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    IsSplitFibredCategory.{vC, uC, vS, max (max uC vC) uS, vS,
      max (max uC vC) uS}
      (strictificationProjection P) := by
  constructor
  · exact strictificationProjection_isFibered P
  · exact strictificationProjection_coGrothendieck_presentation P

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

/-- Reflexivity of equivalence in the 2-category of fibred categories over a
fixed base. -/
theorem isFibredEquivalenceOver_refl
    {S C : Type*} [Category* S] [Category* C] (p : Functor S C) :
    IsFibredEquivalenceOver p p := by
  refine ⟨Functor.id S, Functor.id S, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro X Y f hf
    simpa using hf
  · intro X Y f hf
    simpa using hf
  · refine ⟨Functor.leftUnitor (Functor.id S), rfl, ?_⟩
    intro X
    simp
  · refine ⟨Functor.leftUnitor (Functor.id S), rfl, ?_⟩
    intro X
    simp

/-- Symmetry of equivalence in the 2-category of fibred categories over a
fixed base. -/
theorem isFibredEquivalenceOver_symm
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : Functor S C} {q : Functor T C}
    (h : IsFibredEquivalenceOver p q) :
    IsFibredEquivalenceOver q p := by
  rcases h with ⟨F, G, hF, hG, hFcart, hGcart, hFG, hGF⟩
  exact ⟨G, F, hG, hF, hGcart, hFcart, hGF, hFG⟩

/-- A strict isomorphism over the base is, in particular, an equivalence in
the 2-category of fibred categories over that base. -/
theorem isomorphicOverBase_isFibredEquivalenceOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (h : IsomorphicOverBase p q) :
    IsFibredEquivalenceOver p q := by
  rcases h with ⟨F, G, hF, hG, hFG, hGF⟩
  refine ⟨F, G, hF, hG, ?_, ?_, ?_, ?_⟩
  · intro a b φ hφ
    let : p.IsStronglyCartesian (p.map φ) φ := hφ
    refine { toIsHomLift := ?_, universal_property' := ?_ }
    · infer_instance
    · intro a' g ψ hψ
      have hGa : p.obj (G.obj a') = q.obj a' := Functor.congr_obj hG a'
      have hFa : q.obj (F.obj a) = p.obj a := Functor.congr_obj hF a
      have hFb : q.obj (F.obj b) = p.obj b := Functor.congr_obj hF b
      have hGFa : p.obj (G.obj (F.obj a)) = q.obj (F.obj a) :=
        Functor.congr_obj hG (F.obj a)
      have hGFb : p.obj (G.obj (F.obj b)) = q.obj (F.obj b) :=
        Functor.congr_obj hG (F.obj b)
      have hFGa : G.obj (F.obj a) = a := by
        simpa using congrArg (fun H : S ⥤ S => H.obj a) hFG
      have hFGb : G.obj (F.obj b) = b := by
        simpa using congrArg (fun H : S ⥤ S => H.obj b) hFG
      have hψmap : q.map ψ = g ≫ q.map (F.map φ) := by
        simpa using CategoryTheory.IsHomLift.fac' q
          (g ≫ q.map (F.map φ)) ψ
      have hGψ := Functor.congr_hom hG ψ
      have hFφ := Functor.congr_hom hF φ
      have hGψ' : p.map (G.map ψ) =
          eqToHom hGa ≫ q.map ψ ≫ eqToHom hGFb.symm := by
        simpa only [Functor.comp_map] using hGψ
      have hFφ' : q.map (F.map φ) =
          eqToHom hFa ≫ p.map φ ≫ eqToHom hFb.symm := by
        simpa only [Functor.comp_map] using hFφ
      have hFGbP : p.obj (G.obj (F.obj b)) = p.obj b := congrArg p.obj hFGb
      let gS : p.obj (G.obj a') ⟶ p.obj a :=
        eqToHom hGa ≫ g ≫ eqToHom hFa
      let ψS : G.obj a' ⟶ b :=
        G.map ψ ≫ eqToHom hFGb
      have hψS : p.IsHomLift (gS ≫ p.map φ) ψS := by
        apply CategoryTheory.IsHomLift.of_fac' p (gS ≫ p.map φ) ψS rfl rfl
        dsimp [ψS]
        rw [Functor.map_comp]
        rw [hGψ', hψmap, hFφ']
        have hloop :
            eqToHom hFb.symm ≫ eqToHom hGFb.symm ≫
              p.map (eqToHom hFGb) = 𝟙 (p.obj b) := by
          rw [eqToHom_map]
          simp only [eqToHom_trans]
          congr 1
        simp only [Category.assoc]
        rw [hloop]
        simp [gS]
      have hmapS : p.map ψS = gS ≫ p.map φ := by
        simpa using CategoryTheory.IsHomLift.fac' p (gS ≫ p.map φ) ψS
      let : p.IsHomLift (p.map ψS) ψS := hmapS ▸ hψS
      obtain ⟨δ, ⟨hδ, hδeq⟩, hδuniq⟩ :=
        Functor.IsStronglyCartesian.universal_property p
          (p.map φ) φ gS (p.map ψS) hmapS ψS
      have hGF_a : F.obj (G.obj a') = a' := by
        simpa using congrArg (fun H : T ⥤ T => H.obj a') hGF
      have hF_Ga : q.obj (F.obj (G.obj a')) = p.obj (G.obj a') :=
        Functor.congr_obj hF (G.obj a')
      have hGF_a_q : q.obj (F.obj (G.obj a')) = q.obj a' :=
        congrArg q.obj hGF_a
      have hFδ := Functor.congr_hom hF δ
      have hFδ' : q.map (F.map δ) =
          eqToHom hF_Ga ≫ p.map δ ≫ eqToHom hFa.symm := by
        simpa only [Functor.comp_map] using hFδ
      have hδmap : p.map δ = gS := by
        simpa using CategoryTheory.IsHomLift.fac' p gS δ
      let χ : a' ⟶ F.obj a :=
        eqToHom hGF_a.symm ≫ F.map δ
      have hχmap : q.map χ = g := by
        dsimp [χ]
        rw [Functor.map_comp, eqToHom_map, hFδ', hδmap]
        simp [gS, Category.assoc, eqToHom_trans]
      let : q.IsHomLift g χ := by
        apply CategoryTheory.IsHomLift.of_fac' q g χ rfl rfl
        simpa using hχmap
      have hGF_Fb : F.obj (G.obj (F.obj b)) = F.obj b := by
        simpa using congrArg (fun H : T ⥤ T => H.obj (F.obj b)) hGF
      have hGFψ := Functor.congr_hom hGF ψ
      have hGFψ' : F.map (G.map ψ) =
          eqToHom hGF_a ≫ ψ ≫ eqToHom hGF_Fb.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hGFψ
      have hχeq : χ ≫ F.map φ = ψ := by
        dsimp [χ]
        rw [Category.assoc, ← Functor.map_comp, hδeq]
        dsimp [ψS]
        rw [Functor.map_comp, hGFψ', eqToHom_map]
        simp [Category.assoc, eqToHom_trans]
      refine ⟨χ, ⟨inferInstance, hχeq⟩, ?_⟩
      intro χ' hχ'
      rcases hχ' with ⟨hχ'lift, hχ'eq⟩
      let : q.IsHomLift g χ' := hχ'lift
      have hχ'map : q.map χ' = g := by
        simpa using CategoryTheory.IsHomLift.fac' q g χ'
      have hGχ' := Functor.congr_hom hG χ'
      have hGχ'' : p.map (G.map χ') =
          eqToHom hGa ≫ q.map χ' ≫ eqToHom hGFa.symm := by
        simpa only [Functor.comp_map] using hGχ'
      have hFGaP : p.obj (G.obj (F.obj a)) = p.obj a := congrArg p.obj hFGa
      let δ' : G.obj a' ⟶ a :=
        G.map χ' ≫ eqToHom hFGa
      have hδ'map : p.map δ' = gS := by
        dsimp [δ']
        rw [Functor.map_comp, hGχ'', hχ'map, eqToHom_map]
        simp [gS, Category.assoc, eqToHom_trans]
      have hδ' : p.IsHomLift gS δ' := by
        apply CategoryTheory.IsHomLift.of_fac' p gS δ' rfl rfl
        simpa using hδ'map
      have hFGφ := Functor.congr_hom hFG φ
      have hFGφ' : G.map (F.map φ) =
          eqToHom hFGa ≫ φ ≫ eqToHom hFGb.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hFGφ
      have hδ'eq : δ' ≫ φ = ψS := by
        calc
          δ' ≫ φ = G.map χ' ≫ eqToHom hFGa ≫ φ := by
            simp [δ', Category.assoc]
          _ = (G.map χ' ≫ G.map (F.map φ)) ≫ eqToHom hFGb := by
            rw [hFGφ']
            simp [Category.assoc, eqToHom_trans]
          _ = G.map (χ' ≫ F.map φ) ≫ eqToHom hFGb := by
            rw [Functor.map_comp]
          _ = ψS := by rw [hχ'eq]
      have hδeq' : δ' = δ := hδuniq δ' ⟨hδ', hδ'eq⟩
      have hGF_Fa : F.obj (G.obj (F.obj a)) = F.obj a := by
        simpa using congrArg (fun H : T ⥤ T => H.obj (F.obj a)) hGF
      have hFGaF : F.obj (G.obj (F.obj a)) = F.obj a := congrArg F.obj hFGa
      have hGFχ' := Functor.congr_hom hGF χ'
      have hGFχ'' : F.map (G.map χ') =
          eqToHom hGF_a ≫ χ' ≫ eqToHom hGF_Fa.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hGFχ'
      have hFδ'calc : eqToHom hGF_a.symm ≫ F.map δ' = χ' := by
        dsimp [δ']
        rw [Functor.map_comp, hGFχ'', eqToHom_map]
        simp [Category.assoc, eqToHom_trans]
      calc
        χ' = eqToHom hGF_a.symm ≫ F.map δ' := hFδ'calc.symm
        _ = eqToHom hGF_a.symm ≫ F.map δ := by rw [hδeq']
        _ = χ := rfl
  · intro a b φ hφ
    let : q.IsStronglyCartesian (q.map φ) φ := hφ
    refine { toIsHomLift := ?_, universal_property' := ?_ }
    · infer_instance
    · intro a' g ψ hψ
      have hGa : q.obj (F.obj a') = p.obj a' := Functor.congr_obj hF a'
      have hFa : p.obj (G.obj a) = q.obj a := Functor.congr_obj hG a
      have hFb : p.obj (G.obj b) = q.obj b := Functor.congr_obj hG b
      have hGFa : q.obj (F.obj (G.obj a)) = p.obj (G.obj a) :=
        Functor.congr_obj hF (G.obj a)
      have hGFb : q.obj (F.obj (G.obj b)) = p.obj (G.obj b) :=
        Functor.congr_obj hF (G.obj b)
      have hFGa : F.obj (G.obj a) = a := by
        simpa using congrArg (fun H : T ⥤ T => H.obj a) hGF
      have hFGb : F.obj (G.obj b) = b := by
        simpa using congrArg (fun H : T ⥤ T => H.obj b) hGF
      have hψmap : p.map ψ = g ≫ p.map (G.map φ) := by
        simpa using CategoryTheory.IsHomLift.fac' p
          (g ≫ p.map (G.map φ)) ψ
      have hGψ := Functor.congr_hom hF ψ
      have hGφ := Functor.congr_hom hG φ
      have hGψ' : q.map (F.map ψ) =
          eqToHom hGa ≫ p.map ψ ≫ eqToHom hGFb.symm := by
        simpa only [Functor.comp_map] using hGψ
      have hGφ' : p.map (G.map φ) =
          eqToHom hFa ≫ q.map φ ≫ eqToHom hFb.symm := by
        simpa only [Functor.comp_map] using hGφ
      have hFGbP : q.obj (F.obj (G.obj b)) = q.obj b := congrArg q.obj hFGb
      let gS : q.obj (F.obj a') ⟶ q.obj a :=
        eqToHom hGa ≫ g ≫ eqToHom hFa
      let ψS : F.obj a' ⟶ b :=
        F.map ψ ≫ eqToHom hFGb
      have hψS : q.IsHomLift (gS ≫ q.map φ) ψS := by
        apply CategoryTheory.IsHomLift.of_fac' q (gS ≫ q.map φ) ψS rfl rfl
        dsimp [ψS]
        rw [Functor.map_comp]
        rw [hGψ', hψmap, hGφ']
        have hloop :
            eqToHom hFb.symm ≫ eqToHom hGFb.symm ≫
              q.map (eqToHom hFGb) = 𝟙 (q.obj b) := by
          rw [eqToHom_map]
          simp only [eqToHom_trans]
          congr 1
        simp only [Category.assoc]
        rw [hloop]
        simp [gS]
      have hmapS : q.map ψS = gS ≫ q.map φ := by
        simpa using CategoryTheory.IsHomLift.fac' q (gS ≫ q.map φ) ψS
      let : q.IsHomLift (q.map ψS) ψS := hmapS ▸ hψS
      obtain ⟨δ, ⟨hδ, hδeq⟩, hδuniq⟩ :=
        Functor.IsStronglyCartesian.universal_property q
          (q.map φ) φ gS (q.map ψS) hmapS ψS
      have hGF_a : G.obj (F.obj a') = a' := by
        simpa using congrArg (fun H : S ⥤ S => H.obj a') hFG
      have hF_Ga : p.obj (G.obj (F.obj a')) = q.obj (F.obj a') :=
        Functor.congr_obj hG (F.obj a')
      have hGF_a_q : p.obj (G.obj (F.obj a')) = p.obj a' :=
        congrArg p.obj hGF_a
      have hGδ := Functor.congr_hom hG δ
      have hGδ' : p.map (G.map δ) =
          eqToHom hF_Ga ≫ q.map δ ≫ eqToHom hFa.symm := by
        simpa only [Functor.comp_map] using hGδ
      have hδmap : q.map δ = gS := by
        simpa using CategoryTheory.IsHomLift.fac' q gS δ
      let χ : a' ⟶ G.obj a :=
        eqToHom hGF_a.symm ≫ G.map δ
      have hχmap : p.map χ = g := by
        dsimp [χ]
        rw [Functor.map_comp, eqToHom_map, hGδ', hδmap]
        simp [gS, Category.assoc, eqToHom_trans]
      let : p.IsHomLift g χ := by
        apply CategoryTheory.IsHomLift.of_fac' p g χ rfl rfl
        simpa using hχmap
      have hFG_Fb : G.obj (F.obj (G.obj b)) = G.obj b := by
        simpa using congrArg (fun H : S ⥤ S => H.obj (G.obj b)) hFG
      have hFGψ := Functor.congr_hom hFG ψ
      have hFGψ' : G.map (F.map ψ) =
          eqToHom hGF_a ≫ ψ ≫ eqToHom hFG_Fb.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hFGψ
      have hχeq : χ ≫ G.map φ = ψ := by
        dsimp [χ]
        rw [Category.assoc, ← Functor.map_comp, hδeq]
        dsimp [ψS]
        rw [Functor.map_comp, hFGψ', eqToHom_map]
        simp [Category.assoc, eqToHom_trans]
      refine ⟨χ, ⟨inferInstance, hχeq⟩, ?_⟩
      intro χ' hχ'
      rcases hχ' with ⟨hχ'lift, hχ'eq⟩
      let : p.IsHomLift g χ' := hχ'lift
      have hχ'map : p.map χ' = g := by
        simpa using CategoryTheory.IsHomLift.fac' p g χ'
      have hFχ' := Functor.congr_hom hF χ'
      have hFχ'' : q.map (F.map χ') =
          eqToHom hGa ≫ p.map χ' ≫ eqToHom hGFa.symm := by
        simpa only [Functor.comp_obj, Functor.comp_map] using hFχ'
      have hFGaP : q.obj (F.obj (G.obj a)) = q.obj a := congrArg q.obj hFGa
      let δ' : F.obj a' ⟶ a :=
        F.map χ' ≫ eqToHom hFGa
      have hδ'map : q.map δ' = gS := by
        dsimp [δ']
        rw [Functor.map_comp, hFχ'', hχ'map, eqToHom_map]
        simp [gS, Category.assoc, eqToHom_trans]
      have hδ' : q.IsHomLift gS δ' := by
        apply CategoryTheory.IsHomLift.of_fac' q gS δ' rfl rfl
        simpa using hδ'map
      have hGFφ := Functor.congr_hom hGF φ
      have hGFφ' : F.map (G.map φ) =
          eqToHom hFGa ≫ φ ≫ eqToHom hFGb.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hGFφ
      have hδ'eq : δ' ≫ φ = ψS := by
        calc
          δ' ≫ φ = F.map χ' ≫ eqToHom hFGa ≫ φ := by
            simp [δ', Category.assoc]
          _ = (F.map χ' ≫ F.map (G.map φ)) ≫ eqToHom hFGb := by
            rw [hGFφ']
            simp [Category.assoc, eqToHom_trans]
          _ = F.map (χ' ≫ G.map φ) ≫ eqToHom hFGb := by
            rw [Functor.map_comp]
          _ = ψS := by rw [hχ'eq]
      have hδeq' : δ' = δ := hδuniq δ' ⟨hδ', hδ'eq⟩
      have hFG_Ga : G.obj (F.obj (G.obj a)) = G.obj a := by
        simpa using congrArg (fun H : S ⥤ S => H.obj (G.obj a)) hFG
      have hFGaG : G.obj (F.obj (G.obj a)) = G.obj a := congrArg G.obj hFGa
      have hFGχ' := Functor.congr_hom hFG χ'
      have hFGχ'' : G.map (F.map χ') =
          eqToHom hGF_a ≫ χ' ≫ eqToHom hFG_Ga.symm := by
        simpa only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
          Functor.id_map] using hFGχ'
      have hGδ'calc : eqToHom hGF_a.symm ≫ G.map δ' = χ' := by
        dsimp [δ']
        rw [Functor.map_comp, hFGχ'', eqToHom_map]
        simp [Category.assoc, eqToHom_trans]
      calc
        χ' = eqToHom hGF_a.symm ≫ G.map δ' := hGδ'calc.symm
        _ = eqToHom hGF_a.symm ≫ G.map δ := by rw [hδeq']
        _ = χ := rfl
  · refine ⟨eqToIso hFG, congrArg (fun H : S ⥤ S => H ⋙ p) hFG, ?_⟩
    intro x
    simp [eqToHom_map]
  · refine ⟨eqToIso hGF, congrArg (fun H : T ⥤ T => H ⋙ q) hGF, ?_⟩
    intro x
    simp [eqToHom_map]

/-- Fibred equivalences over a fixed base compose. -/
theorem isFibredEquivalenceOver_trans
    {S T U C : Type*}
    [Category* S] [Category* T] [Category* U] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {r : U ⥤ C}
    (hpq : IsFibredEquivalenceOver p q)
    (hqr : IsFibredEquivalenceOver q r) :
    IsFibredEquivalenceOver p r := by
  rcases hpq with ⟨F, G, hF, hG, hpresF, hpresG, ⟨eFG, overFG, overFGv⟩,
    ⟨eGF, overGF, overGFv⟩⟩
  rcases hqr with ⟨H, K, hH, hK, hpresH, hpresK, ⟨eHK, overHK, overHKv⟩,
    ⟨eKH, overKH, overKHv⟩⟩
  let A : S ⥤ U := F ⋙ H
  let B : U ⥤ S := K ⋙ G
  have hA : A ⋙ r = p := by
    dsimp [A]
    calc
      (F ⋙ H) ⋙ r = F ⋙ (H ⋙ r) := Functor.assoc F H r
      _ = F ⋙ q := by rw [hH]
      _ = p := hF
  have hB : B ⋙ p = r := by
    dsimp [B]
    calc
      (K ⋙ G) ⋙ p = K ⋙ (G ⋙ p) := Functor.assoc K G p
      _ = K ⋙ q := by rw [hG]
      _ = r := hK
  have hpresA : MapsStronglyCartesian p r A := by
    intro a b φ hφ
    have h₁ := hpresF φ hφ
    have h₂ := hpresH (F.map φ) h₁
    simpa [A, Functor.comp_map] using h₂
  have hpresB : MapsStronglyCartesian r p B := by
    intro a b φ hφ
    have h₁ := hpresK φ hφ
    have h₂ := hpresG (K.map φ) h₁
    simpa [B, Functor.comp_map] using h₂
  let eA : A ⋙ B ≅ 𝟭 S :=
    (Functor.associator (F ⋙ H) K G).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator F H K) G ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft F eHK) G ≪≫
      Functor.isoWhiskerRight (Functor.rightUnitor F) G ≪≫ eFG
  let eB : B ⋙ A ≅ 𝟭 U :=
    (Functor.associator (K ⋙ G) F H).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator K G F) H ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft K eGF) H ≪≫
      Functor.isoWhiskerRight (Functor.rightUnitor K) H ≪≫ eKH
  refine ⟨A, B, hA, hB, hpresA, hpresB, ?_, ?_⟩
  · have overA : (A ⋙ B) ⋙ p = (𝟭 S) ⋙ p := by
      calc
        (A ⋙ B) ⋙ p = A ⋙ (B ⋙ p) := Functor.assoc A B p
        _ = A ⋙ r := congrArg (fun X : U ⥤ C => A ⋙ X) hB
        _ = p := hA
        _ = (𝟭 S) ⋙ p := (Functor.id_comp p).symm
    refine ⟨eA, overA, ?_⟩
    intro x
    dsimp [eA]
    simp only [Functor.map_comp]
    have hid1 := p.map_id (G.obj (K.obj (H.obj (F.obj x))))
    have hid2 := p.map_id (G.obj (F.obj x))
    have hGid1 := G.map_id (K.obj (H.obj (F.obj x)))
    have hGid2 := G.map_id (F.obj x)
    rw [hid1, hGid1, hid1, hGid2, hid2]
    rw [Category.id_comp]
    have hGmap :
        p.map (G.map (eHK.hom.app (F.obj x))) =
          eqToHom (Functor.congr_obj hG (K.obj (H.obj (F.obj x)))) ≫
            q.map (eHK.hom.app (F.obj x)) ≫
              eqToHom (Functor.congr_obj hG ((𝟭 T).obj (F.obj x))).symm := by
      simpa only [Functor.comp_map] using
        (Functor.congr_hom hG (eHK.hom.app (F.obj x)))
    rw [hGmap]
    change 𝟙 ((G ⋙ p).obj (K.obj (H.obj (F.obj x)))) ≫ _ = _
    rw [overHKv, overFGv]
    simp
  · have overB : (B ⋙ A) ⋙ r = (𝟭 U) ⋙ r := by
      calc
        (B ⋙ A) ⋙ r = B ⋙ (A ⋙ r) := Functor.assoc B A r
        _ = B ⋙ p := congrArg (fun X : S ⥤ C => B ⋙ X) hA
        _ = r := hB
        _ = (𝟭 U) ⋙ r := (Functor.id_comp r).symm
    refine ⟨eB, overB, ?_⟩
    intro x
    dsimp [eB]
    simp only [Functor.map_comp]
    have hid1 := r.map_id (H.obj (F.obj (G.obj (K.obj x))))
    have hid2 := r.map_id (H.obj (K.obj x))
    have hHid1 := H.map_id (F.obj (G.obj (K.obj x)))
    have hHid2 := H.map_id (K.obj x)
    rw [hid1, hHid1, hid1, hHid2, hid2]
    rw [Category.id_comp]
    have hHmap :
        r.map (H.map (eGF.hom.app (K.obj x))) =
          eqToHom (Functor.congr_obj hH (F.obj (G.obj (K.obj x)))) ≫
            q.map (eGF.hom.app (K.obj x)) ≫
              eqToHom (Functor.congr_obj hH ((𝟭 T).obj (K.obj x))).symm := by
      simpa only [Functor.comp_map] using
        (Functor.congr_hom hH (eGF.hom.app (K.obj x)))
    rw [hHmap]
    change 𝟙 ((H ⋙ r).obj (F.obj (G.obj (K.obj x)))) ≫ _ = _
    rw [overGFv, overKHv]
    simp

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
  map_comp _ _ := rfl

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
      let : p.IsStronglyCartesian (𝟙 (p.obj x))
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

def strictificationFunctor
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    S ⥤ StrictificationCategory p P where
  obj x := strictificationObjectOf P x
  map φ := strictificationFunctorHom P φ
  map_id x := by
    apply StrictificationHom.ext
    change (strictificationFunctorHom P (𝟙 x)).hom = 𝟙 _
    let : p.IsStronglyCartesian (𝟙 (p.obj x))
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
    let : p.IsStronglyCartesian (𝟙 (p.obj Z))
        uZ := P.pullbackMap_isStronglyCartesian _ _
    let : p.IsStronglyCartesian (𝟙 (p.obj Y))
        uY := P.pullbackMap_isStronglyCartesian _ _
    let : p.IsStronglyCartesian (𝟙 (p.obj X))
        uX := P.pullbackMap_isStronglyCartesian _ _
    have hsource_fg : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := by
      simpa using (IsHomLift.comp p (𝟙 (p.obj X)) (p.map (f ≫ g))
        uX (f ≫ g))
    let : p.IsHomLift (p.map (f ≫ g))
        (uX ≫ (f ≫ g)) := hsource_fg
    let : p.IsHomLift (p.map f)
        (strictificationFunctorHom P f).hom :=
      strictificationFunctorHom_isHomLift P f
    let : p.IsHomLift (p.map g)
        (strictificationFunctorHom P g).hom :=
      strictificationFunctorHom_isHomLift P g
    let : p.IsHomLift (p.map f ≫ p.map g)
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
      let : p.IsHomLift (p.map f) (strictificationFunctorHom P f).hom :=
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
        let : p.IsHomLift (p.map φ) h := hhomLift
        let : p.IsStronglyCartesian (p.map φ ≫ 𝟙 (p.obj Y))
            (h ≫ uY) := by simpa using hcompStrong
        let : p.IsStronglyCartesian (𝟙 (p.obj Y)) uY := huY
        exact @Functor.IsStronglyCartesian.of_comp _ _ _ _ p _ _ _ _ _ _
          (p.map φ) (𝟙 (p.obj Y)) h uY huY
          (by simpa using hcompStrong) hhomLift
      let : p.IsStronglyCartesian (p.map φ) h := hstrong
      let : p.IsHomLift (p.map φ) h := hhomLift
      let q := strictificationProjection P
      let : (strictificationProjection P).IsFibered :=
        strictificationProjection_isFibered P
      let κ : (strictificationFunctor P).obj X ⟶
          (strictificationFunctor P).obj Y := strictificationFunctorHom P φ
      have hqmap : q.map κ = p.map φ := by
        dsimp [q, κ, strictificationProjection, StrictificationHom.base,
          h]
        exact (CategoryTheory.IsHomLift.fac p (p.map φ) h).symm
      let : q.IsHomLift (q.map κ) κ := by
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
        let : q.IsHomLift g χ' := by
          have h := (Functor.IsHomLift.map (p := q) χ')
          rw [hχbase] at h
          exact h
        have hχcomp : χ' ≫ κ = τ := by
          apply StrictificationHom.ext
          exact hχfac
        refine ⟨χ', ⟨inferInstance, hχcomp⟩, ?_⟩
        intro χ'' hχ''
        let : q.IsHomLift g χ'' := hχ''.1
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
      let : q.IsFibered := strictificationProjection_isFibered P
      let : q.IsStronglyCartesian (q.map f) f := hf
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
      let : p.IsStronglyCartesian (𝟙 (p.obj Z)) uZ :=
        P.pullbackMap_isStronglyCartesian (𝟙 (p.obj Z)) xZ
      change p.IsHomLift (g ≫ p.map f.hom) τ at hτ
      let : p.IsHomLift (g ≫ p.map f.hom) τ := hτ
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
            simp [Category.assoc]
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
      let : IsIso uZ :=
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
          simp [vZ]
        rw [huZmap] at hv
        apply (cancel_mono (eqToHom eK)).1
        simpa [Category.assoc] using hv
      let : q.IsHomLift G χ := hχ
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
      let : p.IsHomLift g δ' := hδ'.1
      have hδ'map : p.map δ' = g :=
        (CategoryTheory.IsHomLift.eq_of_isHomLift p g δ').symm
      let χ' : K ⟶ A := { hom := uZ ≫ δ' }
      have hχ'map_base :
          eqToHom eK.symm ≫ p.map (uZ ≫ δ') ≫ eqToHom eA =
            g ≫ eqToHom eA := by
        rw [Functor.map_comp, huZmap, hδ'map]
        simp [Category.assoc]
      have hχ'map : q.map χ' = G := by
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
        let : p.IsHomLift (p.map f)
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
          let : p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationPullback A).1))) wA := by
            change p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
            exact P.pullbackMap_isStronglyCartesian _ _
          let : p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationPullback B).1))) wB := by
            change p.IsStronglyCartesian
              (𝟙 (p.obj ((strictificationInverse P).obj B))) wB
            exact P.pullbackMap_isStronglyCartesian _ _
          let : p.IsHomLift (p.map f.hom) f.hom := by
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
          let : p.IsHomLift (p.map f.hom) (wA ≫ f.hom) := hsource
          let : p.IsHomLift
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
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj B))) wB :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
          convert h using 1 ;
            simp
        have hwB : p.map wB = eqToHom eB' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj B))) wB
          convert h using 1 ;
            simp
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
        let : p.IsStronglyCartesian
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA :=
          P.pullbackMap_isStronglyCartesian _ _
        have hwA : p.map wA = eqToHom eA' := by
          have h := CategoryTheory.IsHomLift.fac' p
            (𝟙 (p.obj ((strictificationInverse P).obj A))) wA
          convert h using 1 ;
            simp
        dsimp [e, NatIso.ofComponents, component, comp,
          strictificationProjection, StrictificationHom.base]
        change eqToHom eA'.symm ≫ p.map wA ≫ eqToHom eA0 =
          eqToHom eA0
        rw [hwA]
        simp
  }⟩

/-- The explicit strictification admits a split presentation through a
fibred equivalence. This packages the precise bridge needed by the final
strictification theorem: `strictificationProjection_isSplit` supplies a
strict isomorphism over the base, and
`isomorphicOverBase_isFibredEquivalenceOver` promotes it to the
cartesian-preserving 2-categorical interface. -/
theorem strictificationProjection_fibredEquivalence_to_split
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    {p : S ⥤ C} [p.IsFibered] (P : PullbackChoice p) :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, max (max uC vC) uS},
      IsFibredEquivalenceOver (strictificationProjection P)
        (splitFibredProjection F) := by
  rcases strictificationProjection_isSplit P with ⟨_, F, hF⟩
  exact ⟨F, isomorphicOverBase_isFibredEquivalenceOver hF⟩

theorem fibred_category_equivalent_to_split
    {S : Type uS} [Category.{vS} S]
    {C : Type uC} [Category.{vC} C]
    (p : S ⥤ C) [p.IsFibered] :
    ∃ F : Cᵒᵖ ⥤ Cat.{vS, max (max uC vC) uS},
      IsFibredEquivalenceOver p (splitFibredProjection F) := by
  let P : PullbackChoice p := PullbackChoice.default p
  obtain ⟨D⟩ := strictification_comparison_exists p P
  obtain ⟨F, hF⟩ :=
    strictificationProjection_fibredEquivalence_to_split P
  exact ⟨F, isFibredEquivalenceOver_trans
    (strictificationComparison_isFibredEquivalence D) hF⟩

/-! ## The universe-polymorphic fibred 2-Yoneda comparison -/

/-- A universe-polymorphic fibred morphism.  Unlike the fixed-`Cat` wrapper,
the total categories and the base may live in independent universes. -/
structure FibredMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) where
  functor : S ⥤ T
  over : functor ⋙ q = p
  preserves : MapsStronglyCartesian p q functor

namespace FibredMorphism

/-- Composition of universe-polymorphic fibred functors over a fixed base. -/
def comp
    {S T R C : Type*} [Category* S] [Category* T] [Category* R] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {r : R ⥤ C}
    (F : FibredMorphism p q) (G : FibredMorphism q r) :
    FibredMorphism p r where
  functor := F.functor ⋙ G.functor
  over := by
    calc
      (F.functor ⋙ G.functor) ⋙ r = F.functor ⋙ (G.functor ⋙ r) := by
        simp [Functor.assoc]
      _ = F.functor ⋙ q := by rw [G.over]
      _ = p := F.over
  preserves := by
    intro a b f hf
    exact G.preserves (F.functor.map f) (F.preserves f hf)

/-- The identity universe-polymorphic fibred functor. -/
def id
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) :
    FibredMorphism p p where
  functor := 𝟭 S
  over := Functor.id_comp p
  preserves := by
    intro a b f hf
    simpa using hf

end FibredMorphism

/-- A natural isomorphism between functors over a base is vertical when its
components map to the equality transports determined by the two triangles. -/
def IsFibredNatIsoOver
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : B ⥤ C) {F G : A ⥤ B} (over : F ⋙ q = G ⋙ q) (e : F ≅ G) : Prop :=
  ∀ Z : A,
    q.map (e.hom.app Z) =
      eqToHom (congrArg (fun H : A ⥤ C => H.obj Z) over)

/-- A fixed fibred functor is an equivalence over the base when it admits a
cartesian-preserving inverse and vertical unit and counit isomorphisms. -/
def IsFibredEquivalenceOverMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} (F : FibredMorphism p q) : Prop :=
  ∃ G : FibredMorphism q p,
    (∃ (e : F.functor ⋙ G.functor ≅ 𝟭 S)
      (over : (F.functor ⋙ G.functor) ⋙ p = (𝟭 S) ⋙ p),
      IsFibredNatIsoOver p over e) ∧
    (∃ (e : G.functor ⋙ F.functor ≅ 𝟭 T)
      (over : (G.functor ⋙ F.functor) ⋙ q = (𝟭 T) ⋙ q),
      IsFibredNatIsoOver q over e)

/-- The unbundled existence predicate and the fixed-map predicate describe
the same notion of equivalence over a base.  This is the canonical bridge
for downstream developments: they should use `FibredMorphism` rather than
introducing a second, fieldwise-identical bundle. -/
theorem isFibredEquivalenceOver_iff_exists_fibredMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) :
    IsFibredEquivalenceOver p q ↔
      ∃ F : FibredMorphism p q, IsFibredEquivalenceOverMap F := by
  constructor
  · rintro ⟨F, G, hF, hG, hFcart, hGcart, hFG, hGF⟩
    refine ⟨{ functor := F, over := hF, preserves := hFcart }, ?_⟩
    exact ⟨{ functor := G, over := hG, preserves := hGcart }, hFG, hGF⟩
  · rintro ⟨F, G, hFG, hGF⟩
    exact ⟨F.functor, G.functor, F.over, G.over, F.preserves, G.preserves,
      hFG, hGF⟩

/-- A represented fibred category together with both directions of its
equivalence with the representing slice.  Keeping the strict triangles and
vertical unit and counit makes the construction independent of universe
coincidences between the total and base categories. -/
structure FibredSlicePresentation
    {S C : Type*} [Category* S] [Category* C] (p : S ⥤ C) where
  representingObject : C
  forward : FibredMorphism p (Over.forget representingObject)
  inverse : FibredMorphism (Over.forget representingObject) p
  unit : forward.functor ⋙ inverse.functor ≅ 𝟭 S
  unit_over : (forward.functor ⋙ inverse.functor) ⋙ p = (𝟭 S) ⋙ p
  unit_isOver : IsFibredNatIsoOver p unit_over unit
  counit : inverse.functor ⋙ forward.functor ≅ 𝟭 (Over representingObject)
  counit_over :
    (inverse.functor ⋙ forward.functor) ⋙ Over.forget representingObject =
      (𝟭 (Over representingObject)) ⋙ Over.forget representingObject
  counit_isOver : IsFibredNatIsoOver (Over.forget representingObject)
    counit_over counit

/-- Package a fixed equivalence over the base as a slice presentation. -/
noncomputable def FibredSlicePresentation.ofEquivalenceOverMap
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} (X : C) (F : FibredMorphism p (Over.forget X))
    (hF : IsFibredEquivalenceOverMap F) : FibredSlicePresentation p := by
  let G := Classical.choose hF
  have hG := Classical.choose_spec hF
  exact
    { representingObject := X
      forward := F
      inverse := G
      unit := Classical.choose hG.1
      unit_over := Classical.choose (Classical.choose_spec hG.1)
      unit_isOver := Classical.choose_spec (Classical.choose_spec hG.1)
      counit := Classical.choose hG.2
      counit_over := Classical.choose (Classical.choose_spec hG.2)
      counit_isOver := Classical.choose_spec (Classical.choose_spec hG.2) }

/-- A vertical natural transformation between fibred morphisms.  This is the
universe-polymorphic version of the 2-morphisms used in the fixed-base
2-category. -/
def FibredMorphismNatTrans
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : FibredMorphism p q} (η : F.functor ⟶ G.functor) : Prop :=
  ∀ Z : S,
    q.map (η.app Z) =
      eqToHom (congrArg (fun H : S ⥤ C => H.obj Z)
        (F.over.trans G.over.symm))

/-- Vertical natural isomorphism is the equivalence relation on fibred
morphisms used by the 2-Yoneda comparison. -/
def FibredMorphismTwoIsomorphismRelation
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (F G : FibredMorphism p q) : Prop :=
  ∃ η : F.functor ⟶ G.functor, FibredMorphismNatTrans η ∧ IsIso η

/-- Fibred morphisms modulo vertical natural isomorphism. -/
abbrev FibredMorphismsModuloTwoIsomorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    (p : S ⥤ C) (q : T ⥤ C) :=
  Quot (FibredMorphismTwoIsomorphismRelation (p := p) (q := q))

theorem fibredMorphismNatTrans_comp
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G H : FibredMorphism p q}
    {η : F.functor ⟶ G.functor} {θ : G.functor ⟶ H.functor}
    (hη : FibredMorphismNatTrans η) (hθ : FibredMorphismNatTrans θ) :
    FibredMorphismNatTrans (η ≫ θ) := by
  intro Z
  change q.map (η.app Z ≫ θ.app Z) = _
  rw [Functor.map_comp, hη Z, hθ Z]
  simp only [eqToHom_trans]

theorem fibredMorphismNatTrans_inv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    {F G : FibredMorphism p q} (η : F.functor ⟶ G.functor)
    (hη : FibredMorphismNatTrans η) [IsIso η] :
    FibredMorphismNatTrans (inv η) := by
  intro Z
  apply (cancel_mono (q.map (η.app Z))).1
  rw [← q.map_comp]
  have hinv : (inv η).app Z ≫ η.app Z = 𝟙 _ := by
    exact congrArg (fun τ => τ.app Z) (IsIso.inv_hom_id η)
  rw [hinv, q.map_id, hη Z]
  simp

theorem fibredMorphismTwoIsomorphismRelation_isEquivalence
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} :
    Equivalence
      (FibredMorphismTwoIsomorphismRelation (p := p) (q := q)) := by
  constructor
  · intro F
    refine ⟨𝟙 F.functor, ?_, inferInstance⟩
    intro Z
    simp
  · intro F G hFG
    rcases hFG with ⟨η, hη, hηiso⟩
    refine ⟨inv η, fibredMorphismNatTrans_inv η hη, inferInstance⟩
  · intro F G H hFG hGH
    rcases hFG with ⟨η, hη, hηiso⟩
    rcases hGH with ⟨θ, hθ, hθiso⟩
    refine ⟨η ≫ θ, fibredMorphismNatTrans_comp hη hθ, inferInstance⟩

/-- The functor induced on a fibre by a universe-polymorphic fibred
morphism. -/
def fibredMorphismFiberFunctor
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} (F : FibredMorphism p q) (U : C) :
    Functor.Fiber p U ⥤ Functor.Fiber q U where
  obj x :=
    ⟨F.functor.obj x.1,
      (congrArg (fun H : S ⥤ C => H.obj x.1) F.over).trans x.2⟩
  map {x y} f :=
    ⟨F.functor.map f.1, by
      let hx := (congrArg (fun H : S ⥤ C => H.obj x.1) F.over).trans x.2
      let hy := (congrArg (fun H : S ⥤ C => H.obj y.1) F.over).trans y.2
      exact IsHomLift.of_commsq q (𝟙 U) (F.functor.map f.1) hx hy <|
        by
          simpa [hx, hy,
            @IsHomLift.fac' _ _ _ _ p U U x.1 y.1 (𝟙 U) f.1 f.2,
            Category.assoc] using
            congrArg (fun k => k ≫ eqToHom y.2)
              ((eqToIso F.over).hom.naturality f.1)⟩
  map_id := by
    intro x
    apply Functor.Fiber.hom_ext
    change F.functor.map (𝟙 x.1) = 𝟙 (F.functor.obj x.1)
    simp
  map_comp := by
    intro x y z f g
    apply Functor.Fiber.hom_ext
    change F.functor.map (f.1 ≫ g.1) =
      F.functor.map f.1 ≫ F.functor.map g.1
    simp

/-- The well-defined map on isomorphism classes of objects in each fibre. -/
noncomputable def fibredMorphismObjectClassMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} (F : FibredMorphism p q) (U : C) :
    ThinSkeleton (Functor.Fiber p U) → ThinSkeleton (Functor.Fiber q U) :=
  (ThinSkeleton.map (fibredMorphismFiberFunctor F U)).obj

/-- Any functor between slices that is strictly over the base is vertically
isomorphic to the functor induced by a unique candidate base morphism. -/
theorem sliceFunctorOverBase_isomorphicToMap
    {C : Type*} [Category* C] {X Y : C}
    (F : Over X ⥤ Over Y)
    (hF : F ⋙ Over.forget Y = Over.forget X) :
    ∃ f : X ⟶ Y, ∃ e : F ≅ Over.map f,
      ∃ over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y,
        IsFibredNatIsoOver (Over.forget Y) over e := by
  let hobj : ∀ U : Over X, (F.obj U).left = U.left := fun U =>
    Functor.congr_obj hF U
  let f : X ⟶ Y :=
    eqToHom (hobj (Over.mk (𝟙 X))).symm ≫
      (F.obj (Over.mk (𝟙 X))).hom
  let eapp : ∀ U : Over X, F.obj U ≅ (Over.map f).obj U := fun U => by
    refine Over.isoMk (eqToIso (hobj U)) ?_
    let u : U ⟶ Over.mk (𝟙 X) := Over.homMk U.hom
    have hu := Functor.congr_hom hF u
    change (F.map u).left =
      eqToHom (hobj U) ≫ u.left ≫
        eqToHom (hobj (Over.mk (𝟙 X))).symm at hu
    rw [← Over.w (F.map u), hu]
    dsimp [f, u]
    simp [Category.assoc]
  let e : F ≅ Over.map f := NatIso.ofComponents eapp (by
    intro U V k
    apply (Over.forget Y).map_injective
    have hk := Functor.congr_hom hF k
    change (F.map k).left =
      eqToHom (hobj U) ≫ k.left ≫ eqToHom (hobj V).symm at hk
    change (F.map k).left ≫ eqToHom (hobj V) =
      eqToHom (hobj U) ≫ k.left
    rw [hk]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id])
  let over : F ⋙ Over.forget Y = (Over.map f) ⋙ Over.forget Y :=
    hF.trans (Over.mapForget_eq f).symm
  refine ⟨f, e, over, ?_⟩
  intro U
  change (eapp U).hom.left =
    eqToHom (congrArg (fun L : Over X ⥤ C => L.obj U) over)
  dsimp [e, eapp, over, hobj]
  simp

/-- The unbundled verticality predicate, useful while constructing a fibred
morphism before its cartesian-preservation field is packaged. -/
def FibredNatTransOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G : S ⥤ T}
    (F_over : F ⋙ q = p) (G_over : G ⋙ q = p) (η : F ⟶ G) : Prop :=
  ∀ Z : S,
    q.map (η.app Z) =
      eqToHom (congrArg (fun H : S ⥤ C => H.obj Z)
        (F_over.trans G_over.symm))

theorem fibredNatTransOver_comp
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G H : S ⥤ T}
    {F_over : F ⋙ q = p} {G_over : G ⋙ q = p} {H_over : H ⋙ q = p}
    {η : F ⟶ G} {θ : G ⟶ H}
    (hη : FibredNatTransOver F_over G_over η)
    (hθ : FibredNatTransOver G_over H_over θ) :
    FibredNatTransOver F_over H_over (η ≫ θ) := by
  intro Z
  change q.map (η.app Z ≫ θ.app Z) = _
  rw [Functor.map_comp, hη Z, hθ Z]
  simp only [eqToHom_trans]

theorem fibredNatTransOver_inv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G : S ⥤ T}
    {F_over : F ⋙ q = p} {G_over : G ⋙ q = p}
    (η : F ⟶ G) (hη : FibredNatTransOver F_over G_over η) [IsIso η] :
    FibredNatTransOver G_over F_over (inv η) := by
  intro Z
  apply (cancel_mono (q.map (η.app Z))).1
  rw [← q.map_comp]
  have hinv : (inv η).app Z ≫ η.app Z = 𝟙 _ := by
    exact congrArg (fun τ => τ.app Z) (IsIso.inv_hom_id η)
  rw [hinv, q.map_id, hη Z]
  simp

theorem isFibredNatIsoOver_comp
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : B ⥤ C) {F G H : A ⥤ B}
    (e : F ≅ G) (over : F ⋙ q = G ⋙ q)
    (he : IsFibredNatIsoOver q over e)
    (e' : G ≅ H) (over' : G ⋙ q = H ⋙ q)
    (he' : IsFibredNatIsoOver q over' e') :
    IsFibredNatIsoOver q (over.trans over') (e ≪≫ e') := by
  intro Z
  change q.map (e.hom.app Z ≫ e'.hom.app Z) = _
  rw [Functor.map_comp, he Z, he' Z]
  simp only [eqToHom_trans]

theorem isFibredNatIsoOver_symm
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : B ⥤ C) {F G : A ⥤ B}
    (e : F ≅ G) (over : F ⋙ q = G ⋙ q)
    (he : IsFibredNatIsoOver q over e) :
    IsFibredNatIsoOver q over.symm e.symm := by
  intro Z
  change q.map (e.inv.app Z) = _
  apply (cancel_mono (q.map (e.hom.app Z))).1
  rw [← q.map_comp]
  have hinv : e.inv.app Z ≫ e.hom.app Z = 𝟙 _ := by
    exact congrArg (fun τ => τ.app Z) e.inv_hom_id
  rw [hinv, q.map_id, he Z]
  simp

theorem isFibredNatIsoOver_whiskerLeft
    {A B C D : Type*} [Category* A] [Category* B]
      [Category* C] [Category* D]
    (q : B ⥤ C) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (he : IsFibredNatIsoOver q over e)
    (L : D ⥤ A) :
    IsFibredNatIsoOver q
      ((Functor.assoc L F q).trans
        ((congrArg (fun K : A ⥤ C => L ⋙ K) over).trans
          (Functor.assoc L G q).symm))
      (Functor.isoWhiskerLeft L e) := by
  intro Z
  change q.map (e.hom.app (L.obj Z)) = _
  simpa only [eqToHom_trans] using he (L.obj Z)

theorem isFibredNatIsoOver_whiskerRight
    {A B C D : Type*} [Category* A] [Category* B]
      [Category* C] [Category* D]
    (q : B ⥤ C) {F G : A ⥤ B} (e : F ≅ G)
    (over : F ⋙ q = G ⋙ q) (he : IsFibredNatIsoOver q over e)
    (L : B ⥤ D) (r : D ⥤ C) (L_over : L ⋙ r = q) :
    IsFibredNatIsoOver r
      ((Functor.assoc F L r).trans
        (((congrArg (fun K : B ⥤ C => F ⋙ K) L_over).trans
          (over.trans
            (congrArg (fun K : B ⥤ C => G ⋙ K) L_over.symm))).trans
          (Functor.assoc G L r).symm))
      (Functor.isoWhiskerRight e L) := by
  intro Z
  change r.map (L.map (e.hom.app Z)) = _
  have hL := Functor.congr_hom L_over (e.hom.app Z)
  change (L ⋙ r).map (e.hom.app Z) = _
  rw [hL, he Z]
  simp only [eqToHom_trans]

/-- The functor underlying the lift of a morphism between representing
objects. -/
def fibredSliceLiftFunctor
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) : S ⥤ T :=
  P.forward.functor ⋙ Over.map φ ⋙ Q.inverse.functor

theorem fibredSliceLiftFunctor_over
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    fibredSliceLiftFunctor P Q φ ⋙ q = p := by
  calc
    fibredSliceLiftFunctor P Q φ ⋙ q =
        P.forward.functor ⋙ Over.map φ ⋙ (Q.inverse.functor ⋙ q) := by
      simp [fibredSliceLiftFunctor, Functor.assoc]
    _ = P.forward.functor ⋙ Over.map φ ⋙
        Over.forget Q.representingObject := by rw [Q.inverse.over]
    _ = P.forward.functor ⋙ Over.forget P.representingObject := by
      simpa [Functor.assoc] using congrArg
        (fun K : Over P.representingObject ⥤ C => P.forward.functor ⋙ K)
        (Over.mapForget_eq φ)
    _ = p := P.forward.over

theorem fibredSliceLiftFunctor_preserves
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) :
    MapsStronglyCartesian p q (fibredSliceLiftFunctor P Q φ) := by
  intro a b f hf
  exact Q.inverse.preserves ((Over.map φ).map (P.forward.functor.map f))
    (hφ (P.forward.functor.map f) (P.forward.preserves f hf))

/-- The inverse 2-Yoneda lift of a morphism between representing objects. -/
def fibredSliceLift
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) :
    FibredMorphism p q where
  functor := fibredSliceLiftFunctor P Q φ
  over := fibredSliceLiftFunctor_over P Q φ
  preserves := fibredSliceLiftFunctor_preserves P Q φ hφ

/-- Essential surjectivity of the represented 2-Yoneda comparison: every
functor over the base is vertically isomorphic to a lift of a morphism of
representing objects. -/
theorem fibredSlicePresentation_liftFunctorComparison
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : S ⥤ T) (F_over : F ⋙ q = p) :
    ∃ φ : P.representingObject ⟶ Q.representingObject,
      ∃ η : F ⟶ fibredSliceLiftFunctor P Q φ,
        FibredNatTransOver F_over (fibredSliceLiftFunctor_over P Q φ) η ∧
          IsIso η := by
  let H : Over P.representingObject ⥤ Over Q.representingObject :=
    P.inverse.functor ⋙ F ⋙ Q.forward.functor
  have hH : H ⋙ Over.forget Q.representingObject =
      Over.forget P.representingObject := by
    dsimp [H]
    calc
      (P.inverse.functor ⋙ F ⋙ Q.forward.functor) ⋙
          Over.forget Q.representingObject =
          P.inverse.functor ⋙ F ⋙ q := by
            simpa [Functor.assoc] using congrArg
              (fun K : T ⥤ C => (P.inverse.functor ⋙ F) ⋙ K)
              Q.forward.over
      _ = P.inverse.functor ⋙ p := by
        simpa [Functor.assoc] using congrArg
          (fun K : S ⥤ C => P.inverse.functor ⋙ K) F_over
      _ = Over.forget P.representingObject := P.inverse.over
  obtain ⟨φ, eH, overH, heH⟩ :=
    sliceFunctorOverBase_isomorphicToMap H hH
  let eP_over :
      (P.forward.functor ⋙ H) ⋙ Over.forget Q.representingObject =
        (F ⋙ Q.forward.functor) ⋙ Over.forget Q.representingObject := by
    calc
      (P.forward.functor ⋙ H) ⋙ Over.forget Q.representingObject =
          P.forward.functor ⋙ (H ⋙ Over.forget Q.representingObject) := by
            simp [Functor.assoc]
      _ = P.forward.functor ⋙ Over.forget P.representingObject := by rw [hH]
      _ = p := P.forward.over
      _ = F ⋙ q := F_over.symm
      _ = F ⋙ (Q.forward.functor ⋙
          Over.forget Q.representingObject) := by rw [Q.forward.over]
      _ = (F ⋙ Q.forward.functor) ⋙
          Over.forget Q.representingObject := by simp [Functor.assoc]
  let eP : P.forward.functor ⋙ H ≅ F ⋙ Q.forward.functor :=
    (Functor.associator P.forward.functor P.inverse.functor
      (F ⋙ Q.forward.functor)).symm ≪≫
      Functor.isoWhiskerRight P.unit (F ⋙ Q.forward.functor) ≪≫
      Functor.leftUnitor (F ⋙ Q.forward.functor)
  have heP : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eP_over eP := by
    intro Z
    dsimp [eP]
    simp only [Category.comp_id]
    have hQmap := Functor.congr_hom Q.forward.over
      (F.map (P.unit.hom.app Z))
    have hFmap := Functor.congr_hom F_over (P.unit.hom.app Z)
    calc
      _ = (Q.forward.functor ⋙ Over.forget Q.representingObject).map
          (F.map (P.unit.hom.app Z)) := by
            simpa only [Functor.comp_map, Functor.comp_obj,
              Over.forget_map, Over.forget_obj] using
              (Category.id_comp (Over.Hom.left
                (Q.forward.functor.map (F.map (P.unit.hom.app Z)))))
      _ = _ := hQmap
      _ = _ := by
        have hFmap' : q.map (F.map (P.unit.hom.app Z)) =
            eqToHom (congrArg (fun K : S ⥤ C => K.obj
              ((P.forward.functor ⋙ P.inverse.functor).obj Z)) F_over) ≫
              p.map (P.unit.hom.app Z) ≫
              eqToHom (congrArg (fun K : S ⥤ C => K.obj Z) F_over).symm := by
          simpa only [Functor.comp_map] using hFmap
        rw [hFmap', P.unit_isOver Z]
        simp only [eqToHom_trans]
        rfl
  let eFB : F ⋙ Q.forward.functor ≅
      P.forward.functor ⋙ Over.map φ :=
    eP.symm ≪≫ Functor.isoWhiskerLeft P.forward.functor eH
  let eFB_over :
      (F ⋙ Q.forward.functor) ⋙ Over.forget Q.representingObject =
        (P.forward.functor ⋙ Over.map φ) ⋙
          Over.forget Q.representingObject := by
    calc
      (F ⋙ Q.forward.functor) ⋙ Over.forget Q.representingObject =
          F ⋙ q := by simp [Functor.assoc, Q.forward.over]
      _ = p := F_over
      _ = P.forward.functor ⋙ Over.forget P.representingObject :=
        P.forward.over.symm
      _ = (P.forward.functor ⋙ Over.map φ) ⋙
          Over.forget Q.representingObject := by
        symm
        simpa [Functor.assoc] using congrArg
          (fun K : Over P.representingObject ⥤ C => P.forward.functor ⋙ K)
          (Over.mapForget_eq φ)
  have hePInv : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eP_over.symm eP.symm :=
    isFibredNatIsoOver_symm (Over.forget Q.representingObject)
      eP eP_over heP
  have heHLeft : IsFibredNatIsoOver (Over.forget Q.representingObject)
      _ (Functor.isoWhiskerLeft P.forward.functor eH) :=
    isFibredNatIsoOver_whiskerLeft
      (Over.forget Q.representingObject) eH overH heH P.forward.functor
  have heFB' := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) eP.symm eP_over.symm hePInv
      (Functor.isoWhiskerLeft P.forward.functor eH) _ heHLeft
  have heFB : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eFB_over eFB := by
    simpa [eFB, eFB_over] using heFB'
  let eF : F ≅ fibredSliceLiftFunctor P Q φ := by
    simpa [fibredSliceLiftFunctor, Functor.assoc] using
      (((Functor.rightUnitor F).symm ≪≫
          Functor.isoWhiskerLeft F Q.unit.symm) ≪≫
        (Functor.associator F Q.forward.functor Q.inverse.functor).symm) ≪≫
          Functor.isoWhiskerRight eFB Q.inverse.functor
  let eRight_over : F ⋙ q = (F ⋙ 𝟭 T) ⋙ q := by
    rw [Functor.assoc, Functor.id_comp]
  have heRight : IsFibredNatIsoOver q eRight_over
      (Functor.rightUnitor F).symm := by
    intro Z
    simp
  have heQUnitInv : IsFibredNatIsoOver q Q.unit_over.symm Q.unit.symm :=
    isFibredNatIsoOver_symm q Q.unit Q.unit_over Q.unit_isOver
  let eQUnitLeft_over :
      (F ⋙ 𝟭 T) ⋙ q = (F ⋙
        (Q.forward.functor ⋙ Q.inverse.functor)) ⋙ q :=
    (Functor.assoc F (𝟭 T) q).trans
      ((congrArg (fun K : T ⥤ C => F ⋙ K) Q.unit_over.symm).trans
        (Functor.assoc F
          (Q.forward.functor ⋙ Q.inverse.functor) q).symm)
  have heQUnitLeft : IsFibredNatIsoOver q eQUnitLeft_over
      (Functor.isoWhiskerLeft F Q.unit.symm) :=
    isFibredNatIsoOver_whiskerLeft q Q.unit.symm Q.unit_over.symm
      heQUnitInv F
  let eAssoc_over :
      (F ⋙ (Q.forward.functor ⋙ Q.inverse.functor)) ⋙ q =
        ((F ⋙ Q.forward.functor) ⋙ Q.inverse.functor) ⋙ q := by
    simp [Functor.assoc]
  have heAssoc : IsFibredNatIsoOver q eAssoc_over
      (Functor.associator F Q.forward.functor Q.inverse.functor).symm := by
    intro Z
    simp
  have heFBRight : IsFibredNatIsoOver q _
      (Functor.isoWhiskerRight eFB Q.inverse.functor) :=
    isFibredNatIsoOver_whiskerRight
      (Over.forget Q.representingObject) eFB eFB_over heFB
      Q.inverse.functor q Q.inverse.over
  have heF' := isFibredNatIsoOver_comp q
    (Functor.rightUnitor F).symm eRight_over heRight
      (Functor.isoWhiskerLeft F Q.unit.symm) _ heQUnitLeft
  have heF'' := isFibredNatIsoOver_comp q
    ((Functor.rightUnitor F).symm ≪≫
        Functor.isoWhiskerLeft F Q.unit.symm)
      (eRight_over.trans eQUnitLeft_over) heF'
      (Functor.associator F Q.forward.functor Q.inverse.functor).symm
      eAssoc_over heAssoc
  have heF''' := isFibredNatIsoOver_comp q
    (((Functor.rightUnitor F).symm ≪≫
        Functor.isoWhiskerLeft F Q.unit.symm) ≪≫
          (Functor.associator F Q.forward.functor Q.inverse.functor).symm)
      ((eRight_over.trans eQUnitLeft_over).trans eAssoc_over) heF''
      (Functor.isoWhiskerRight eFB Q.inverse.functor) _ heFBRight
  have heF : FibredNatTransOver F_over
      (fibredSliceLiftFunctor_over P Q φ) eF.hom := by
    intro Z
    simpa [eF, fibredSliceLiftFunctor, Functor.assoc] using heF''' Z
  exact ⟨φ, eF.hom, heF, inferInstance⟩

/-- Bundled essential surjectivity, with the chosen lift carrying its
cartesian-preservation proof. -/
theorem fibredSlicePresentation_liftComparison
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (F : FibredMorphism p q) :
    ∃ φ : P.representingObject ⟶ Q.representingObject,
      FibredMorphismTwoIsomorphismRelation F
        (fibredSliceLift P Q φ (hmap φ)) := by
  obtain ⟨φ, η, hη, hηiso⟩ :=
    fibredSlicePresentation_liftFunctorComparison P Q F.functor F.over
  refine ⟨φ, η, ?_, hηiso⟩
  exact hη

/-- A vertical natural isomorphism between two slice maps remembers the base
morphism uniquely. -/
theorem sliceMap_eq_of_verticalIso
    {C : Type*} [Category* C] {X Y : C} {φ ψ : X ⟶ Y}
    (e : Over.map φ ≅ Over.map ψ)
    (over : (Over.map φ) ⋙ Over.forget Y =
      (Over.map ψ) ⋙ Over.forget Y)
    (he : IsFibredNatIsoOver (Over.forget Y) over e) : φ = ψ := by
  let u : Over X := Over.mk (𝟙 X)
  have hleft : (e.hom.app u).left = 𝟙 X := by
    have hv := he u
    have heq : congrArg (fun L : Over X ⥤ C => L.obj u) over = rfl :=
      Subsingleton.elim _ _
    have hv' : (e.hom.app u).left =
        eqToHom (congrArg (fun L : Over X ⥤ C => L.obj u) over) := by
      simpa only [Functor.comp_obj, Over.forget_obj, Over.forget_map] using hv
    have hid : eqToHom
        (congrArg (fun L : Over X ⥤ C => L.obj u) over) = 𝟙 X := by
      apply CategoryTheory.eqToHom_refl
    rw [hid] at hv'
    simpa [u] using hv'
  have hw := Over.w (e.hom.app u)
  dsimp [u] at hw
  rw [hleft] at hw
  simpa only [Category.id_comp] using hw.symm

/-- Conjugate a functor between represented fibred categories into a functor
between their representing slices. -/
def fibredSliceTransport
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : S ⥤ T) : Over P.representingObject ⥤ Over Q.representingObject :=
  P.inverse.functor ⋙ F ⋙ Q.forward.functor

theorem fibredSliceTransport_over
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : S ⥤ T) (F_over : F ⋙ q = p) :
    fibredSliceTransport P Q F ⋙ Over.forget Q.representingObject =
      Over.forget P.representingObject := by
  dsimp [fibredSliceTransport]
  calc
    (P.inverse.functor ⋙ F ⋙ Q.forward.functor) ⋙
        Over.forget Q.representingObject =
        P.inverse.functor ⋙ F ⋙ q := by
          simpa [Functor.assoc] using congrArg
            (fun K : T ⥤ C => (P.inverse.functor ⋙ F) ⋙ K)
            Q.forward.over
    _ = P.inverse.functor ⋙ p := by
      simpa [Functor.assoc] using congrArg
        (fun K : S ⥤ C => P.inverse.functor ⋙ K) F_over
    _ = Over.forget P.representingObject := P.inverse.over

/-- The morphism of representing objects extracted from a fibred morphism. -/
noncomputable def fibredSliceRepresentingMorphism
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : FibredMorphism p q) :
    P.representingObject ⟶ Q.representingObject :=
  Classical.choose (sliceFunctorOverBase_isomorphicToMap
    (fibredSliceTransport P Q F.functor)
    (fibredSliceTransport_over P Q F.functor F.over))

theorem fibredSliceRepresentingMorphism_spec
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (F : FibredMorphism p q) :
    ∃ e : fibredSliceTransport P Q F.functor ≅
        Over.map (fibredSliceRepresentingMorphism P Q F),
      ∃ over : fibredSliceTransport P Q F.functor ⋙
          Over.forget Q.representingObject =
        Over.map (fibredSliceRepresentingMorphism P Q F) ⋙
          Over.forget Q.representingObject,
        IsFibredNatIsoOver (Over.forget Q.representingObject) over e := by
  exact Classical.choose_spec (sliceFunctorOverBase_isomorphicToMap
    (fibredSliceTransport P Q F.functor)
    (fibredSliceTransport_over P Q F.functor F.over))

/-- Cancelling the two presentation equivalences identifies the conjugate of
a lifted morphism with the corresponding slice map. -/
noncomputable def fibredSliceLiftTransportIso
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    fibredSliceTransport P Q (fibredSliceLiftFunctor P Q φ) ≅ Over.map φ := by
  simpa [fibredSliceTransport, fibredSliceLiftFunctor, Functor.assoc] using
    ((Functor.isoWhiskerRight P.counit
        (Over.map φ ⋙ (Q.inverse.functor ⋙ Q.forward.functor)) ≪≫
      Functor.leftUnitor
        (Over.map φ ⋙ (Q.inverse.functor ⋙ Q.forward.functor))) ≪≫
      (Functor.isoWhiskerLeft (Over.map φ) Q.counit ≪≫
        Functor.rightUnitor (Over.map φ)))

theorem fibredSliceLiftTransportIso_isOver
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject) :
    IsFibredNatIsoOver (Over.forget Q.representingObject)
      ((fibredSliceTransport_over P Q (fibredSliceLiftFunctor P Q φ)
        (fibredSliceLiftFunctor_over P Q φ)).trans
          (Over.mapForget_eq φ).symm)
      (fibredSliceLiftTransportIso P Q φ) := by
  let K : Over P.representingObject ⥤ Over Q.representingObject :=
    Over.map φ ⋙ (Q.inverse.functor ⋙ Q.forward.functor)
  have hK : K ⋙ Over.forget Q.representingObject =
      Over.forget P.representingObject := by
    calc
      K ⋙ Over.forget Q.representingObject =
          Over.map φ ⋙ ((Q.inverse.functor ⋙ Q.forward.functor) ⋙
            Over.forget Q.representingObject) := by
              simp [K, Functor.assoc]
      _ = Over.map φ ⋙ ((𝟭 (Over Q.representingObject)) ⋙
          Over.forget Q.representingObject) := by rw [Q.counit_over]
      _ = Over.map φ ⋙ Over.forget Q.representingObject := by
        rw [Functor.id_comp]
      _ = Over.forget P.representingObject := Over.mapForget_eq φ
  let eP := Functor.isoWhiskerRight P.counit K
  have heP := isFibredNatIsoOver_whiskerRight
    (Over.forget P.representingObject) P.counit P.counit_over
      P.counit_isOver K (Over.forget Q.representingObject) hK
  let eLeft := Functor.leftUnitor K
  let eLeft_over : (𝟭 (Over P.representingObject) ⋙ K) ⋙
      Over.forget Q.representingObject =
      K ⋙ Over.forget Q.representingObject := by
    exact (Functor.assoc _ _ _).trans (Functor.id_comp _)
  have heLeft : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eLeft_over eLeft := by
    intro Z
    change 𝟙 _ = eqToHom _
    symm
    apply CategoryTheory.eqToHom_refl
  have hePL := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) eP _ heP eLeft eLeft_over heLeft
  let eQ := Functor.isoWhiskerLeft (Over.map φ) Q.counit
  have heQ := isFibredNatIsoOver_whiskerLeft
    (Over.forget Q.representingObject) Q.counit Q.counit_over
      Q.counit_isOver (Over.map φ)
  let eRight := Functor.rightUnitor (Over.map φ)
  let eRight_over : (Over.map φ ⋙ 𝟭 (Over Q.representingObject)) ⋙
      Over.forget Q.representingObject =
      Over.map φ ⋙ Over.forget Q.representingObject := by
    exact (Functor.assoc _ _ _).trans (congrArg
      (fun L : Over Q.representingObject ⥤ C => Over.map φ ⋙ L)
      (Functor.id_comp _))
  have heRight : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eRight_over eRight := by
    intro Z
    change 𝟙 _ = eqToHom _
    symm
    apply CategoryTheory.eqToHom_refl
  have heQR := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) eQ _ heQ eRight eRight_over heRight
  have he := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) (eP ≪≫ eLeft) _ hePL
      (eQ ≪≫ eRight) _ heQR
  change IsFibredNatIsoOver (Over.forget Q.representingObject) _
    ((eP ≪≫ eLeft) ≪≫ (eQ ≪≫ eRight))
  exact he

theorem fibredSliceRepresentingMorphism_lift
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) :
    fibredSliceRepresentingMorphism P Q (fibredSliceLift P Q φ hφ) = φ := by
  obtain ⟨e, over, he⟩ :=
    fibredSliceRepresentingMorphism_spec P Q (fibredSliceLift P Q φ hφ)
  let overφ :=
    (fibredSliceTransport_over P Q (fibredSliceLiftFunctor P Q φ)
      (fibredSliceLiftFunctor_over P Q φ)).trans
        (Over.mapForget_eq φ).symm
  have heInv : IsFibredNatIsoOver (Over.forget Q.representingObject)
      over.symm e.symm :=
    isFibredNatIsoOver_symm (Over.forget Q.representingObject) e over he
  have heφ := fibredSliceLiftTransportIso_isOver P Q φ
  have heComp := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) e.symm over.symm heInv
      (fibredSliceLiftTransportIso P Q φ) overφ heφ
  exact sliceMap_eq_of_verticalIso
    (e.symm ≪≫ fibredSliceLiftTransportIso P Q φ)
      (over.symm.trans overφ) heComp

/-- The representing morphism depends only on the vertical-isomorphism class
of a fibred morphism. -/
theorem fibredSliceRepresentingMorphism_eq_of_twoIsomorphic
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    {F G : FibredMorphism p q}
    (hFG : FibredMorphismTwoIsomorphismRelation F G) :
    fibredSliceRepresentingMorphism P Q F =
      fibredSliceRepresentingMorphism P Q G := by
  rcases hFG with ⟨η, hη, hηiso⟩
  let _ : IsIso η := hηiso
  let eη : F.functor ≅ G.functor := asIso η
  have heη : IsFibredNatIsoOver q (F.over.trans G.over.symm) eη := hη
  let eηLeft := Functor.isoWhiskerLeft P.inverse.functor eη
  have heηLeft := isFibredNatIsoOver_whiskerLeft q eη
    (F.over.trans G.over.symm) heη P.inverse.functor
  let eηTransport := Functor.isoWhiskerRight eηLeft Q.forward.functor
  have heηTransport := isFibredNatIsoOver_whiskerRight q eηLeft _
    heηLeft Q.forward.functor (Over.forget Q.representingObject)
      Q.forward.over
  let overη : fibredSliceTransport P Q F.functor ⋙
      Over.forget Q.representingObject =
      fibredSliceTransport P Q G.functor ⋙
        Over.forget Q.representingObject :=
    (fibredSliceTransport_over P Q F.functor F.over).trans
      (fibredSliceTransport_over P Q G.functor G.over).symm
  have heηTransport' : IsFibredNatIsoOver
      (Over.forget Q.representingObject) overη eηTransport := heηTransport
  obtain ⟨eF, overF, heF⟩ := fibredSliceRepresentingMorphism_spec P Q F
  obtain ⟨eG, overG, heG⟩ := fibredSliceRepresentingMorphism_spec P Q G
  have heFInv := isFibredNatIsoOver_symm
    (Over.forget Q.representingObject) eF overF heF
  have he₁ := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) eF.symm overF.symm heFInv
      eηTransport overη heηTransport'
  have he₂ := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) (eF.symm ≪≫ eηTransport) _ he₁
      eG overG heG
  exact sliceMap_eq_of_verticalIso ((eF.symm ≪≫ eηTransport) ≪≫ eG)
    (overF.symm.trans (overη.trans overG))
    he₂

/-- The forward map on 2-isomorphism classes. -/
noncomputable def fibredSliceMorphismClassToHom
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q) :
    FibredMorphismsModuloTwoIsomorphism p q →
      (P.representingObject ⟶ Q.representingObject) :=
  Quot.lift (fibredSliceRepresentingMorphism P Q)
    (fun _ _ h => fibredSliceRepresentingMorphism_eq_of_twoIsomorphic P Q h)

/-- The inverse map sends a morphism of representing objects to the class of
its lifted fibred morphism. -/
def fibredSliceHomToMorphismClass
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (φ : P.representingObject ⟶ Q.representingObject) :
    FibredMorphismsModuloTwoIsomorphism p q :=
  Quot.mk _ (fibredSliceLift P Q φ (hmap φ))

/-- Universe-polymorphic full faithfulness of the represented fibred-category
construction, on fibred morphisms modulo vertical natural isomorphism. -/
noncomputable def fibredSliceMorphismClassesEquiv
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ)) :
    FibredMorphismsModuloTwoIsomorphism p q ≃
      (P.representingObject ⟶ Q.representingObject) where
  toFun := fibredSliceMorphismClassToHom P Q
  invFun := fibredSliceHomToMorphismClass P Q hmap
  left_inv := by
    intro x
    refine Quot.inductionOn x ?_
    intro F
    obtain ⟨φ, hF⟩ := fibredSlicePresentation_liftComparison P Q hmap F
    have hrepr : fibredSliceRepresentingMorphism P Q F = φ :=
      (fibredSliceRepresentingMorphism_eq_of_twoIsomorphic P Q hF).trans
        (fibredSliceRepresentingMorphism_lift P Q φ (hmap φ))
    change Quot.mk _ (fibredSliceLift P Q
      (fibredSliceRepresentingMorphism P Q F)
        (hmap (fibredSliceRepresentingMorphism P Q F))) = Quot.mk _ F
    subst hrepr
    exact (Quot.sound hF).symm
  right_inv := by
    intro φ
    exact fibredSliceRepresentingMorphism_lift P Q φ (hmap φ)

/-- Vertically isomorphic fibred morphisms induce the same map on object
classes in every fibre. -/
theorem fibredMorphismObjectClassMap_eq_of_natIso
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G : FibredMorphism p q}
    (e : F.functor ≅ G.functor) (hη : FibredMorphismNatTrans e.hom)
    (U : C) :
    fibredMorphismObjectClassMap F U = fibredMorphismObjectClassMap G U := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  change ThinSkeleton.mk ((fibredMorphismFiberFunctor F U).obj x) =
    ThinSkeleton.mk ((fibredMorphismFiberFunctor G U).obj x)
  apply Quotient.sound
  have hηinv : FibredMorphismNatTrans e.inv := by
    simpa using fibredMorphismNatTrans_inv e.hom hη
  let hx : q.obj (F.functor.obj x.1) = U :=
    (congrArg (fun H : S ⥤ C => H.obj x.1) F.over).trans x.2
  let hy : q.obj (G.functor.obj x.1) = U :=
    (congrArg (fun H : S ⥤ C => H.obj x.1) G.over).trans x.2
  let k : (fibredMorphismFiberFunctor F U).obj x ⟶
      (fibredMorphismFiberFunctor G U).obj x := by
    refine ⟨e.hom.app x.1, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac' q (𝟙 U) (e.hom.app x.1) hx hy
    simpa [hx, hy, eqToHom_trans] using hη x.1
  let l : (fibredMorphismFiberFunctor G U).obj x ⟶
      (fibredMorphismFiberFunctor F U).obj x := by
    refine ⟨e.inv.app x.1, ?_⟩
    apply CategoryTheory.IsHomLift.of_fac' q (𝟙 U) (e.inv.app x.1) hy hx
    simpa [hx, hy, eqToHom_trans] using hηinv x.1
  exact ⟨{
    hom := k
    inv := l
    hom_inv_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun τ => τ.app x.1) e.hom_inv_id
    inv_hom_id := by
      apply Functor.Fiber.hom_ext
      exact congrArg (fun τ => τ.app x.1) e.inv_hom_id }⟩

theorem fibredMorphismObjectClassMap_comp
    {S T R C : Type*} [Category* S] [Category* T] [Category* R] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {r : R ⥤ C}
    (F : FibredMorphism p q) (G : FibredMorphism q r) (U : C) :
    fibredMorphismObjectClassMap (FibredMorphism.comp F G) U =
      fibredMorphismObjectClassMap G U ∘
        fibredMorphismObjectClassMap F U := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  change ThinSkeleton.mk
      ((fibredMorphismFiberFunctor (FibredMorphism.comp F G) U).obj x) =
    ThinSkeleton.mk
      ((fibredMorphismFiberFunctor G U).obj
        ((fibredMorphismFiberFunctor F U).obj x))
  congr 1

theorem fibredMorphismObjectClassMap_id
    {S C : Type*} [Category* S] [Category* C]
    (p : S ⥤ C) (U : C) :
    fibredMorphismObjectClassMap (FibredMorphism.id p) U = id := by
  funext z
  refine Quotient.inductionOn z ?_
  intro x
  change ThinSkeleton.mk
      ((fibredMorphismFiberFunctor (FibredMorphism.id p) U).obj x) =
    ThinSkeleton.mk x
  congr 1

/-- A slice map as a bundled fibred morphism, given its cartesian-preservation
proof. -/
def sliceMapFibredMorphism
    {C : Type*} [Category* C] {X Y : C} (φ : X ⟶ Y)
    (hφ : MapsStronglyCartesian (Over.forget X) (Over.forget Y) (Over.map φ)) :
    FibredMorphism (Over.forget X) (Over.forget Y) where
  functor := Over.map φ
  over := Over.mapForget_eq φ
  preserves := hφ

/-- After applying the target presentation, a lifted morphism is vertically
isomorphic to the corresponding slice map after the source presentation. -/
noncomputable def fibredSliceLiftForwardIso
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) :
    (fibredSliceLift P Q φ hφ).functor ⋙ Q.forward.functor ≅
      P.forward.functor ⋙ Over.map φ := by
  simpa [fibredSliceLift, fibredSliceLiftFunctor, Functor.assoc] using
    (Functor.isoWhiskerLeft (P.forward.functor ⋙ Over.map φ) Q.counit ≪≫
      Functor.rightUnitor (P.forward.functor ⋙ Over.map φ))

theorem fibredSliceLiftForwardIso_isFibredMorphismNatTrans
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) :
    FibredMorphismNatTrans
      (F := FibredMorphism.comp (fibredSliceLift P Q φ hφ) Q.forward)
      (G := FibredMorphism.comp P.forward (sliceMapFibredMorphism φ hφ))
      (fibredSliceLiftForwardIso P Q φ hφ).hom := by
  let L := P.forward.functor ⋙ Over.map φ
  let eQ := Functor.isoWhiskerLeft L Q.counit
  have heQ := isFibredNatIsoOver_whiskerLeft
    (Over.forget Q.representingObject) Q.counit Q.counit_over
      Q.counit_isOver L
  let eQ_over : (L ⋙ (Q.inverse.functor ⋙ Q.forward.functor)) ⋙
      Over.forget Q.representingObject =
      (L ⋙ 𝟭 (Over Q.representingObject)) ⋙
        Over.forget Q.representingObject :=
    (Functor.assoc L (Q.inverse.functor ⋙ Q.forward.functor)
      (Over.forget Q.representingObject)).trans
        ((congrArg (fun K : Over Q.representingObject ⥤ C => L ⋙ K)
          Q.counit_over).trans
            (Functor.assoc L (𝟭 (Over Q.representingObject))
              (Over.forget Q.representingObject)).symm)
  have heQ' : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eQ_over eQ := heQ
  let eRight := Functor.rightUnitor L
  let eRight_over : (L ⋙ 𝟭 (Over Q.representingObject)) ⋙
      Over.forget Q.representingObject =
      L ⋙ Over.forget Q.representingObject := by
    exact (Functor.assoc _ _ _).trans (congrArg
      (fun K : Over Q.representingObject ⥤ C => L ⋙ K)
      (Functor.id_comp _))
  have heRight : IsFibredNatIsoOver (Over.forget Q.representingObject)
      eRight_over eRight := by
    intro Z
    change 𝟙 _ = eqToHom _
    symm
    apply CategoryTheory.eqToHom_refl
  have he := isFibredNatIsoOver_comp
    (Over.forget Q.representingObject) eQ eQ_over heQ'
      eRight eRight_over heRight
  have heq : fibredSliceLiftForwardIso P Q φ hφ = eQ ≪≫ eRight := by
    simp [fibredSliceLiftForwardIso, fibredSliceLift,
      fibredSliceLiftFunctor, L, eQ, eRight, Functor.assoc]
  rw [heq]
  exact he

/-- The inverse lift has exactly the object-class map induced by the
representing slice morphism. -/
theorem fibredSliceLift_objectClassMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hφ : MapsStronglyCartesian (Over.forget P.representingObject)
      (Over.forget Q.representingObject) (Over.map φ)) (U : C) :
    fibredMorphismObjectClassMap Q.forward U ∘
        fibredMorphismObjectClassMap (fibredSliceLift P Q φ hφ) U =
      fibredMorphismObjectClassMap (sliceMapFibredMorphism φ hφ) U ∘
        fibredMorphismObjectClassMap P.forward U := by
  have h := fibredMorphismObjectClassMap_eq_of_natIso
    (F := FibredMorphism.comp (fibredSliceLift P Q φ hφ) Q.forward)
    (G := FibredMorphism.comp P.forward (sliceMapFibredMorphism φ hφ))
    (fibredSliceLiftForwardIso P Q φ hφ)
    (fibredSliceLiftForwardIso_isFibredMorphismNatTrans P Q φ hφ) U
  simpa only [fibredMorphismObjectClassMap_comp] using h

theorem fibredSlicePresentation_forward_inverse_objectClassMap
    {S C : Type*} [Category* S] [Category* C]
    {p : S ⥤ C} (P : FibredSlicePresentation p) (U : C) :
    fibredMorphismObjectClassMap P.forward U ∘
        fibredMorphismObjectClassMap P.inverse U = id := by
  have hnat : FibredMorphismNatTrans
      (F := FibredMorphism.comp P.inverse P.forward)
      (G := FibredMorphism.id (Over.forget P.representingObject))
      P.counit.hom := P.counit_isOver
  have h := fibredMorphismObjectClassMap_eq_of_natIso
    (F := FibredMorphism.comp P.inverse P.forward)
    (G := FibredMorphism.id (Over.forget P.representingObject))
    P.counit hnat U
  simpa only [fibredMorphismObjectClassMap_comp,
    fibredMorphismObjectClassMap_id] using h

theorem sliceMap_eq_of_objectClassMap_eq
    {C : Type*} [Category* C] {X Y : C} {φ ψ : X ⟶ Y}
    (hφ : MapsStronglyCartesian (Over.forget X) (Over.forget Y) (Over.map φ))
    (hψ : MapsStronglyCartesian (Over.forget X) (Over.forget Y) (Over.map ψ))
    (h : fibredMorphismObjectClassMap (sliceMapFibredMorphism φ hφ) X =
      fibredMorphismObjectClassMap (sliceMapFibredMorphism ψ hψ) X) :
    φ = ψ := by
  let u : Functor.Fiber (Over.forget X) X := ⟨Over.mk (𝟙 X), rfl⟩
  have hu := congrFun h (ThinSkeleton.mk u)
  change ThinSkeleton.mk
      ((fibredMorphismFiberFunctor (sliceMapFibredMorphism φ hφ) X).obj u) =
    ThinSkeleton.mk
      ((fibredMorphismFiberFunctor (sliceMapFibredMorphism ψ hψ) X).obj u) at hu
  obtain ⟨e⟩ := (Quotient.exact hu)
  have hleft : e.hom.1.left = 𝟙 X := by
    let _ : (Over.forget Y).IsHomLift (𝟙 X) e.hom.1 := e.hom.2
    have he := CategoryTheory.IsHomLift.fac' (Over.forget Y) (𝟙 X) e.hom.1
    change e.hom.1.left = _ at he
    rw [he]
    simp only [Category.id_comp, eqToHom_trans]
    apply CategoryTheory.eqToHom_refl
  have hw := Over.w e.hom.1
  dsimp [fibredMorphismFiberFunctor, sliceMapFibredMorphism, u] at hw
  rw [hleft] at hw
  simpa using hw.symm

/-- The extracted representing morphism gives the same fibrewise object-class
map as the original fibred morphism. -/
theorem fibredSliceRepresentingMorphism_objectClassMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (F : FibredMorphism p q) (U : C) :
    fibredMorphismObjectClassMap Q.forward U ∘
        fibredMorphismObjectClassMap F U =
      fibredMorphismObjectClassMap
          (sliceMapFibredMorphism (fibredSliceRepresentingMorphism P Q F)
            (hmap (fibredSliceRepresentingMorphism P Q F))) U ∘
        fibredMorphismObjectClassMap P.forward U := by
  obtain ⟨φ, η, hη, hηiso⟩ :=
    fibredSlicePresentation_liftComparison P Q hmap F
  let _ : IsIso η := hηiso
  let e : F.functor ≅ (fibredSliceLift P Q φ (hmap φ)).functor := asIso η
  have hclasses := fibredMorphismObjectClassMap_eq_of_natIso e hη U
  have hrepr : fibredSliceRepresentingMorphism P Q F = φ :=
    (fibredSliceRepresentingMorphism_eq_of_twoIsomorphic P Q
      ⟨η, hη, hηiso⟩).trans
      (fibredSliceRepresentingMorphism_lift P Q φ (hmap φ))
  rw [hclasses]
  simpa only [hrepr] using fibredSliceLift_objectClassMap P Q φ (hmap φ) U

/-- Equality of represented object-class maps detects the extracted
representing morphism. -/
theorem fibredSliceRepresentingMorphism_eq_of_objectClassMap
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (F : FibredMorphism p q)
    (φ : P.representingObject ⟶ Q.representingObject)
    (hF : ∀ U : C,
      fibredMorphismObjectClassMap Q.forward U ∘
          fibredMorphismObjectClassMap F U =
        fibredMorphismObjectClassMap (sliceMapFibredMorphism φ (hmap φ)) U ∘
          fibredMorphismObjectClassMap P.forward U) :
    fibredSliceRepresentingMorphism P Q F = φ := by
  let ψ := fibredSliceRepresentingMorphism P Q F
  have hcomp : fibredMorphismObjectClassMap
        (sliceMapFibredMorphism ψ (hmap ψ)) P.representingObject ∘
        fibredMorphismObjectClassMap P.forward P.representingObject =
      fibredMorphismObjectClassMap
        (sliceMapFibredMorphism φ (hmap φ)) P.representingObject ∘
        fibredMorphismObjectClassMap P.forward P.representingObject := by
    rw [← fibredSliceRepresentingMorphism_objectClassMap P Q hmap F,
      ← hF]
  have hsec := fibredSlicePresentation_forward_inverse_objectClassMap
    P P.representingObject
  have hslices : fibredMorphismObjectClassMap
        (sliceMapFibredMorphism ψ (hmap ψ)) P.representingObject =
      fibredMorphismObjectClassMap
        (sliceMapFibredMorphism φ (hmap φ)) P.representingObject := by
    funext z
    have hz := congrFun hcomp
      (fibredMorphismObjectClassMap P.inverse P.representingObject z)
    have hzsec := congrFun hsec z
    change fibredMorphismObjectClassMap P.forward P.representingObject
        (fibredMorphismObjectClassMap P.inverse P.representingObject z) = z
      at hzsec
    simpa only [Function.comp_apply, hzsec] using hz
  exact sliceMap_eq_of_objectClassMap_eq (hmap ψ) (hmap φ) hslices

/-- In setoid fibres, a vertical natural transformation between two fixed
fibred morphisms is unique. -/
theorem fibredMorphismNatTrans_unique_of_fibreHomSubsingleton
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C} {F G : FibredMorphism p q}
    (hhom : ∀ (U : C) (X Y : Functor.Fiber q U),
      Subsingleton (X ⟶ Y))
    {η θ : F.functor ⟶ G.functor}
    (hη : FibredMorphismNatTrans η) (hθ : FibredMorphismNatTrans θ) :
    η = θ := by
  apply NatTrans.ext
  funext Z
  let hx : q.obj (F.functor.obj Z) = p.obj Z :=
    congrArg (fun H : S ⥤ C => H.obj Z) F.over
  let hy : q.obj (G.functor.obj Z) = p.obj Z :=
    congrArg (fun H : S ⥤ C => H.obj Z) G.over
  let η' : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hy :=
    ⟨η.app Z, by
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 (p.obj Z))
        (η.app Z) hx hy
      simpa [hx, hy, eqToHom_trans] using hη Z⟩
  let θ' : Functor.Fiber.mk hx ⟶ Functor.Fiber.mk hy :=
    ⟨θ.app Z, by
      apply CategoryTheory.IsHomLift.of_fac' q (𝟙 (p.obj Z))
        (θ.app Z) hx hy
      simpa [hx, hy, eqToHom_trans] using hθ Z⟩
  have hηθ : η' = θ' := (hhom (p.obj Z) _ _).elim _ _
  exact congrArg (fun k => k.1) hηθ

/-- Full faithfulness before quotienting: fibred morphisms with the same
representing morphism admit a unique vertical natural isomorphism. -/
theorem fibredSlicePresentation_uniqueNatIso_of_representingMorphism_eq
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (hhom : ∀ (U : C) (X Y : Functor.Fiber q U),
      Subsingleton (X ⟶ Y))
    {F G : FibredMorphism p q}
    (hrep : fibredSliceRepresentingMorphism P Q F =
      fibredSliceRepresentingMorphism P Q G) :
    ∃! η : F.functor ⟶ G.functor, FibredMorphismNatTrans η ∧ IsIso η := by
  obtain ⟨φ, ηF, hηF, hηFiso⟩ :=
    fibredSlicePresentation_liftComparison P Q hmap F
  obtain ⟨ψ, ηG, hηG, hηGiso⟩ :=
    fibredSlicePresentation_liftComparison P Q hmap G
  let _ : IsIso ηF := hηFiso
  let _ : IsIso ηG := hηGiso
  have hφ : fibredSliceRepresentingMorphism P Q F = φ :=
    (fibredSliceRepresentingMorphism_eq_of_twoIsomorphic P Q
      ⟨ηF, hηF, hηFiso⟩).trans
      (fibredSliceRepresentingMorphism_lift P Q φ (hmap φ))
  have hψ : fibredSliceRepresentingMorphism P Q G = ψ :=
    (fibredSliceRepresentingMorphism_eq_of_twoIsomorphic P Q
      ⟨ηG, hηG, hηGiso⟩).trans
      (fibredSliceRepresentingMorphism_lift P Q ψ (hmap ψ))
  have hφψ : φ = ψ := hφ.symm.trans (hrep.trans hψ)
  have hFrel : FibredMorphismTwoIsomorphismRelation F
      (fibredSliceLift P Q φ (hmap φ)) := ⟨ηF, hηF, hηFiso⟩
  have hGrel : FibredMorphismTwoIsomorphismRelation G
      (fibredSliceLift P Q φ (hmap φ)) := by
    rw [hφψ]
    exact ⟨ηG, hηG, hηGiso⟩
  let heqv :=
    fibredMorphismTwoIsomorphismRelation_isEquivalence (p := p) (q := q)
  have hFG : FibredMorphismTwoIsomorphismRelation F G :=
    heqv.trans hFrel (heqv.symm hGrel)
  rcases hFG with ⟨η, hη, hηiso⟩
  refine ⟨η, ⟨hη, hηiso⟩, ?_⟩
  intro θ hθ
  exact fibredMorphismNatTrans_unique_of_fibreHomSubsingleton
    hhom hθ.1 hη

/-- A fibred morphism induces a specified morphism of representing objects
when their fibrewise maps on object classes agree through the presentations. -/
def FibredMorphismInducesRepresentingMorphismOnObjectClasses
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (F : FibredMorphism p q)
    (φ : P.representingObject ⟶ Q.representingObject) : Prop :=
  ∀ U : C,
    fibredMorphismObjectClassMap Q.forward U ∘
        fibredMorphismObjectClassMap F U =
      fibredMorphismObjectClassMap (sliceMapFibredMorphism φ (hmap φ)) U ∘
        fibredMorphismObjectClassMap P.forward U

/-- Existence and uniqueness before quotienting, in the object-class form
used by representability arguments. -/
theorem fibredSlicePresentation_morphism_existsAndUnique
    {S T C : Type*} [Category* S] [Category* T] [Category* C]
    {p : S ⥤ C} {q : T ⥤ C}
    (P : FibredSlicePresentation p) (Q : FibredSlicePresentation q)
    (hmap : ∀ φ : P.representingObject ⟶ Q.representingObject,
      MapsStronglyCartesian (Over.forget P.representingObject)
        (Over.forget Q.representingObject) (Over.map φ))
    (hhom : ∀ (U : C) (X Y : Functor.Fiber q U),
      Subsingleton (X ⟶ Y))
    (φ : P.representingObject ⟶ Q.representingObject) :
    ∃ F : FibredMorphism p q,
      FibredMorphismInducesRepresentingMorphismOnObjectClasses P Q hmap F φ ∧
        ∀ G : FibredMorphism p q,
          FibredMorphismInducesRepresentingMorphismOnObjectClasses
            P Q hmap G φ →
          ∃! η : F.functor ⟶ G.functor,
            FibredMorphismNatTrans η ∧ IsIso η := by
  let F := fibredSliceLift P Q φ (hmap φ)
  refine ⟨F, ?_, ?_⟩
  · intro U
    exact fibredSliceLift_objectClassMap P Q φ (hmap φ) U
  · intro G hG
    apply fibredSlicePresentation_uniqueNatIso_of_representingMorphism_eq
      P Q hmap hhom
    calc
      fibredSliceRepresentingMorphism P Q F = φ :=
        fibredSliceRepresentingMorphism_lift P Q φ (hmap φ)
      _ = fibredSliceRepresentingMorphism P Q G :=
        (fibredSliceRepresentingMorphism_eq_of_objectClassMap
          P Q hmap G φ hG).symm

end

end Formalization.Books.Categories.Unit36
