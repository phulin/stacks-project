import Formalization.Books.Stacks.Unit01.Foundation
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Stacks, Chapter 1, Section 2: presheaves of morphisms
-/

namespace Formalization.Books.Stacks.Unit01

/- The Mathlib descent presheaf is used as the canonical implementation. -/

open CategoryTheory
open Opposite

universe w v u

abbrev MorphismPresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :=
  MorPresheaf F x y

abbrev IsomorphismPresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :=
  IsomPresheaf F x y

/- The inclusion of the presheaf of isomorphisms into the presheaf of
  morphisms.  The subtype is taken objectwise, so this is the canonical
  subpresheaf occurring in the book. -/
def isomorphismPresheafInclusion {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    IsomorphismPresheaf F x y ⟶ MorphismPresheaf F x y where
  app T := ↾(fun f : (IsomorphismPresheaf F x y).obj T => f.1)
  naturality _ _ q := by
    rfl

theorem mor_presheaf_is_presheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    MorPresheaf F x y = F.presheafHom x y := rfl

def presheaf_mor_map_fibred_categories {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    F.presheafHom x y ⟶
      G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y) := by
  refine { app := fun T => ?_, naturality := ?_ }
  · simpa [Pseudofunctor.presheafHom] using
      (↾(fun f : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
          (F.map T.unop.hom.op.toLoc).toFunctor.obj y =>
        (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app
            x ≫
          (η.app (.mk (op T.unop.left))).toFunctor.map f ≫
            (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app
              y))
  · intro T₁ T₂ q
    ext f
    have hηinv {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
        (fg : a ⟶ c) (hfg : f ≫ g = fg) :
        (η.naturality fg).inv =
          Bicategory.whiskerLeft (η.app a) (G.mapComp' f g fg hfg).hom ≫
            (Bicategory.associator _ _ _).inv ≫
              Bicategory.whiskerRight (η.naturality f).inv (G.map g) ≫
                (Bicategory.associator _ _ _).hom ≫
                  Bicategory.whiskerLeft (F.map f) (η.naturality g).inv ≫
                    (Bicategory.associator _ _ _).inv ≫
                      Bicategory.whiskerRight (F.mapComp' f g fg hfg).inv (η.app c) := by
      subst fg
      simpa only [Pseudofunctor.mapComp'_eq_mapComp] using
        η.naturality_comp_inv f g
    have hηhom {a b c : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) (g : b ⟶ c)
        (fg : a ⟶ c) (hfg : f ≫ g = fg) :
        (η.naturality fg).hom =
          Bicategory.whiskerRight (F.mapComp' f g fg hfg).hom (η.app c) ≫
            (Bicategory.associator _ _ _).hom ≫
              Bicategory.whiskerLeft (F.map f) (η.naturality g).hom ≫
                (Bicategory.associator _ _ _).inv ≫
                  Bicategory.whiskerRight (η.naturality f).hom (G.map g) ≫
                    (Bicategory.associator _ _ _).hom ≫
                      Bicategory.whiskerLeft (η.app a) (G.mapComp' f g fg hfg).inv := by
      subst fg
      simpa only [Pseudofunctor.mapComp'_eq_mapComp] using
        η.naturality_comp_hom f g
    have hfg : T₁.unop.hom.op.toLoc ≫ (Over.Hom.left q.unop).op.toLoc =
        T₂.unop.hom.op.toLoc := by
      rw [← Quiver.Hom.comp_toLoc, ← op_comp, q.unop.w]
    have hFproof (p : T₁.unop.hom.op.toLoc ≫ (Over.Hom.left q.unop).op.toLoc =
        T₂.unop.hom.op.toLoc) :
        F.mapComp' T₁.unop.hom.op.toLoc (Over.Hom.left q.unop).op.toLoc
          T₂.unop.hom.op.toLoc p =
          F.mapComp' T₁.unop.hom.op.toLoc (Over.Hom.left q.unop).op.toLoc
            T₂.unop.hom.op.toLoc hfg := by
      rw [Subsingleton.elim p hfg]
    have hGproof (p : T₁.unop.hom.op.toLoc ≫ (Over.Hom.left q.unop).op.toLoc =
        T₂.unop.hom.op.toLoc) :
        G.mapComp' T₁.unop.hom.op.toLoc (Over.Hom.left q.unop).op.toLoc
          T₂.unop.hom.op.toLoc p =
          G.mapComp' T₁.unop.hom.op.toLoc (Over.Hom.left q.unop).op.toLoc
            T₂.unop.hom.op.toLoc hfg := by
      rw [Subsingleton.elim p hfg]
    dsimp [Pseudofunctor.presheafHom, Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Category.assoc, Functor.map_comp]
    simp only [hηinv _ _ _ hfg, hηhom _ _ _ hfg]
    have hq :=
      (η.naturality (Over.Hom.left q.unop).op.toLoc).inv.toNatTrans.naturality
        f
    simp
    simp only [hFproof, hGproof]
    rw [← (η.app (.mk (op (unop T₂).left))).toFunctor.map_comp_assoc]
    simp only [Cat.Hom.inv_hom_id_toNatTrans_app]
    have hηid :
        (η.app (.mk (op (unop T₂).left))).toFunctor.map
            (𝟙 ((F.map T₁.unop.hom.op.toLoc ≫
              F.map (Over.Hom.left q.unop).op.toLoc).toFunctor.obj x)) = 𝟙 _ := by
      exact (η.app (.mk (op (unop T₂).left))).toFunctor.map_id _
    rw [hηid]
    simp
    nth_rewrite 2 [← (η.app (.mk (op (unop T₂).left))).toFunctor.map_comp_assoc]
    have hFy :
        (η.app (.mk (op (unop T₂).left))).toFunctor.map
            ((Pseudofunctor.mapComp' F T₁.unop.hom.op.toLoc
              (Over.Hom.left q.unop).op.toLoc T₂.unop.hom.op.toLoc hfg).inv.toNatTrans.app y ≫
            (Pseudofunctor.mapComp' F T₁.unop.hom.op.toLoc
              (Over.Hom.left q.unop).op.toLoc T₂.unop.hom.op.toLoc hfg).hom.toNatTrans.app y) = 𝟙 _ := by
      rw [Cat.Hom.inv_hom_id_toNatTrans_app]
      exact (η.app (.mk (op (unop T₂).left))).toFunctor.map_id _
    rw [hFy]
    simp
    have hmid :
        (η.naturality (Over.Hom.left q.unop).op.toLoc).inv.toNatTrans.app
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.obj x) ≫
          (η.app (.mk (op (unop T₂).left))).toFunctor.map
            ((F.map (Over.Hom.left q.unop).op.toLoc).toFunctor.map f) ≫
          (η.naturality (Over.Hom.left q.unop).op.toLoc).hom.toNatTrans.app
            ((F.map T₁.unop.hom.op.toLoc).toFunctor.obj y) =
          (η.app (.mk (op (unop T₁).left)) ≫
          G.map (Over.Hom.left q.unop).op.toLoc).toFunctor.map f := by
      calc
        _ =
            (η.naturality (Over.Hom.left q.unop).op.toLoc).inv.toNatTrans.app
                ((F.map T₁.unop.hom.op.toLoc).toFunctor.obj x) ≫
              (F.map (Over.Hom.left q.unop).op.toLoc ≫
                η.app (.mk (op (unop T₂).left))).toFunctor.map f ≫
                (η.naturality (Over.Hom.left q.unop).op.toLoc).hom.toNatTrans.app
                  ((F.map T₁.unop.hom.op.toLoc).toFunctor.obj y) := by
          simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
        _ = (η.app (.mk (op (unop T₁).left)) ≫
            G.map (Over.Hom.left q.unop).op.toLoc).toFunctor.map f := by
          rw [← Category.assoc, ← hq]
          simp
    simp only [reassoc_of% hmid]
    simp

theorem presheaf_mor_map_fibred_categories_exists {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    Nonempty
      (F.presheafHom x y ⟶
        G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) :=
  ⟨presheaf_mor_map_fibred_categories η x y⟩

theorem isom_presheaf_is_subpresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) (T : (Over C U)ᵒᵖ)
    (f : { f : (F.presheafHom x y).obj T // IsIso f }) : IsIso f.1 := f.2

theorem isomorphism_presheaf_inclusion_app {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ)
    (f : (IsomorphismPresheaf F x y).obj T) :
    (isomorphismPresheafInclusion F x y).app T f = f.1 := by
  simp [isomorphismPresheafInclusion]

structure TwoFiberProductPresentation {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) where
  apex : Pseudofunctor (LocallyDiscrete (Over C U)ᵒᵖ) Cat.{w, w}
  isSetoid : FiberwiseSetoid apex
  presheaf : (Over C U)ᵒᵖ ⥤ Type w
  presheafIso : presheaf ≅ IsomPresheaf F x y

theorem isom_as_two_fibre_product {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    Nonempty (TwoFiberProductPresentation F x y) := by
  let P := IsomPresheaf F x y
  let Q : (Over C U)ᵒᵖ ⥤ Cat := {
    obj := fun T => Cat.of (Discrete (P.obj T))
    map := fun {T₁ T₂} f =>
      (Discrete.functor (fun z => Discrete.mk (P.map f z))).toCatHom
    map_id := fun T => by
      apply Cat.Hom.ext
      apply Discrete.functor_ext
      intro Z
      have hZ : P.map (𝟙 T) Z = Z :=
        congrArg (fun h : P.obj T ⟶ P.obj T => h Z) (P.map_id T)
      exact congrArg Discrete.mk hZ
    map_comp := fun {T₀ T₁ T₂} f g => by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext ?_ ?_
      · intro Z
        have hZ : P.map (f ≫ g) Z.as = P.map g (P.map f Z.as) :=
          congrArg (fun h : P.obj T₀ ⟶ P.obj T₂ => h Z.as) (P.map_comp f g)
        change Discrete.mk (P.map (f ≫ g) Z.as) =
          Discrete.mk (P.map g (P.map f Z.as))
        exact congrArg Discrete.mk hZ
      · intro Z Z' q
        rcases Z with ⟨Z⟩
        rcases Z' with ⟨Z'⟩
        rcases q with ⟨⟨h⟩⟩
        change Z = Z' at h
        subst Z'
        rfl }
  let A : FiberedCategory (Over C U) := Q.toPseudofunctor'
  refine ⟨{ apex := A, isSetoid := ?_, presheaf := P, presheafIso := Iso.refl P }⟩
  constructor <;> intro T
  · change IsGroupoid (Discrete (P.obj (op T)))
    infer_instance
  · change ∀ (X Y : Discrete (P.obj (op T))), Subsingleton (X ⟶ Y)
    infer_instance

theorem isom_presheaf_is_morphism_presheaf_of_groupoid
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    (hF : FiberwiseGroupoid F) {U : C} (x y : Fiber F U) :
    Nonempty (IsomPresheaf F x y ≅ F.presheafHom x y) := by
  refine ⟨NatIso.ofComponents (fun T => ?_) ?_⟩
  · letI : IsGroupoid (Fiber F T.unop.left) := hF _
    refine
      { hom := ↾(fun f : (IsomPresheaf F x y).obj T => f.1)
        inv := ↾(fun f : (F.presheafHom x y).obj T => ⟨f, by infer_instance⟩)
        hom_inv_id := by ext f; rfl
        inv_hom_id := by ext f; rfl }
  · intro T₁ T₂ q
    ext f
    rfl

end Formalization.Books.Stacks.Unit01
