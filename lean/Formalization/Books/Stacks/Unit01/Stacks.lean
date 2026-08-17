import Formalization.Books.Stacks.Unit01.Presheaves
import Formalization.Books.Stacks.Unit01.Descent

/-!
# Stacks, Chapter 1, Section 4: stacks
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

structure StackObject (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  value : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  isStack : Stack value J

structure StackMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (X Y : StackObject C J) where
  map : FiberedMorphism X.value Y.value

def IsStack2Morphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X Y : StackObject C J}
    (f g : StackMorphism X Y) : Prop :=
  Nonempty (f.map ⟶ g.map)

def HasFibrewiseRepresentatives {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Prop :=
    ∀ U : C, ∃ representatives : Set (Fiber F U),
    ∀ X : Fiber F U, ∃ Y, Y ∈ representatives ∧ Nonempty (X ≅ Y)

structure SmallSubstackData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  inclusion : FiberedMorphism value F
  isStack : Stack value J
  fullyFaithful : FiberwiseFullyFaithful inclusion
  essentiallySurjective : FiberwiseEssentiallySurjective inclusion
  hasFibrewiseRepresentatives : HasFibrewiseRepresentatives value

theorem small_stack_substack_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : Stack F J) (hrepresentatives : HasFibrewiseRepresentatives F) :
    Nonempty (SmallSubstackData F J) := by
  refine ⟨⟨F, 𝟙 F, hF, ?_, ?_, hrepresentatives⟩⟩
  · intro U
    change Nonempty ((𝟭 _).FullyFaithful)
    exact ⟨Functor.FullyFaithful.id _⟩
  · intro U
    change Functor.EssSurj (𝟭 _)
    infer_instance

theorem stack_morphism_presheaves_are_sheaves {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C} [F.IsStack J]
    {U : C} (x y : Fiber F U) :
    Presheaf.IsSheaf (J.over U) (F.presheafHom x y) := by
  exact IsPrestack.isSheaf J x y

theorem stack_iff_effective_descent {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Stack F J ↔
      ∀ (U : C) (R : Sieve U), R ∈ J U →
        (F.toDescentData (fun f : R.arrows.category ↦ f.obj.hom)).IsEquivalence := by
  constructor
  · intro h U R hR
    let : F.IsStack J := h
    exact (F.isStackFor' R hR).isEquivalence
  · intro h
    exact Pseudofunctor.IsStack.of_isStackFor (fun S R hR => ⟨h S R hR⟩)

theorem substack_is_stack {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    [F.IsStack J] (S : Substack F J) :
    Stack S.value J := by
  sorry

theorem equivalent_fibred_categories_preserve_stack
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    Stack F J ↔ Stack G J := by
  sorry

theorem two_fibre_product_of_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, Stack P.apex J := by
  exact pointwise_two_fibre_product_of_stacks J hF hG hH f g

theorem characterize_fully_faithful {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {F G : FiberedCategory C}
    (η : FiberedMorphism F G) [F.IsStack J] [G.IsStack J] :
    FiberwiseFullyFaithful η ↔
      ∀ (U : C) (x y : Fiber F U),
        IsIso (presheaf_mor_map_fibred_categories η x y) := by
  constructor
  · intro h U x y
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    dsimp [presheaf_mor_map_fibred_categories]
    rw [isIso_iff_bijective]
    rcases h T.unop.left with ⟨hT⟩
    constructor
    · intro a b hab
      apply hT.map_injective
      apply (cancel_epi
        ((η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x)).1
      apply (cancel_mono
        ((η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y)).1
      change
        (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
            (η.app (.mk (op T.unop.left))).toFunctor.map a ≫
              (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y =
          (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
            (η.app (.mk (op T.unop.left))).toFunctor.map b ≫
              (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y at hab
      simpa only [Category.assoc] using hab
    · intro z
      obtain ⟨a, ha⟩ := hT.map_surjective
        (inv ((η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x) ≫ z ≫
          inv ((η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y))
      refine ⟨a, ?_⟩
      change (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
        (η.app (.mk (op T.unop.left))).toFunctor.map a ≫
          (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y = z
      rw [ha]
      simp [Category.assoc]
  · intro h U
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro x y
    have hxy := (NatTrans.isIso_iff_isIso_app
      (presheaf_mor_map_fibred_categories η x y)).mp (h U x y)
    have hxy0 := hxy (op (Over.mk (𝟙 U)))
    rw [isIso_iff_bijective] at hxy0
    let eF := Cat.Hom.toNatIso (F.mapId (.mk (op U)))
    let eG := Cat.Hom.toNatIso (G.mapId (.mk (op U)))
    have hFid := ((eF.app x).symm.homCongr (eF.app y).symm).bijective
    have hGid :=
      ((eG.app ((η.app (.mk (op U))).toFunctor.obj x)).homCongr
        (eG.app ((η.app (.mk (op U))).toFunctor.obj y))).bijective
    have hcomp := Function.Bijective.comp hGid (hxy0.comp hFid)
    have hEq :
        (η.app (.mk (op U))).toFunctor.map =
          ⇑((eG.app ((η.app (.mk (op U))).toFunctor.obj x)).homCongr
            (eG.app ((η.app (.mk (op U))).toFunctor.obj y))) ∘
            ⇑(ConcreteCategory.hom
              ((presheaf_mor_map_fibred_categories η x y).app
                (op (Over.mk (𝟙 U))))) ∘
              ⇑((eF.app x).symm.homCongr (eF.app y).symm) := by
      funext f
      let f' : x ⟶ y := f
      change (η.app (.mk (op U))).toFunctor.map f' = _
      simp [presheaf_mor_map_fibred_categories,
        Iso.homCongr, eF, eG,
        Function.comp_apply, Cat.Hom.comp_toFunctor,
        CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_inv_app,
        CategoryTheory.Pseudofunctor.StrongTrans.naturality_id_hom_app,
        Cat.Hom.id_toFunctor,
        Equiv.coe_fn_mk, Category.assoc]
      change
        (η.app (.mk (op U))).toFunctor.map f' =
          (G.mapId (.mk (op U))).inv.toNatTrans.app
              ((η.app (.mk (op U))).toFunctor.obj x) ≫
            ((G.mapId (.mk (op U))).hom.toNatTrans.app
                ((η.app (.mk (op U))).toFunctor.obj x) ≫
              (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).inv.toNatTrans.app x) ≫
              (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).hom.toNatTrans.app x ≫ f' ≫
                  (F.mapId (.mk (op U))).inv.toNatTrans.app y) ≫
              (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).hom.toNatTrans.app y) ≫
              (G.mapId (.mk (op U))).inv.toNatTrans.app
                ((η.app (.mk (op U))).toFunctor.obj y)) ≫
            (G.mapId (.mk (op U))).hom.toNatTrans.app
              ((η.app (.mk (op U))).toFunctor.obj y)
      simp only [Functor.map_comp, Category.assoc]
      have hFx :
          (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).inv.toNatTrans.app x) ≫
              (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).hom.toNatTrans.app x) =
            𝟙 _ := by
        calc
          _ = (η.app (.mk (op U))).toFunctor.map
              (𝟙 ((𝟭 (F.obj (.mk (op U)))).obj x)) := by
            simpa only [Functor.map_comp, Cat.Hom.id_toFunctor] using
              congrArg (fun k => (η.app (.mk (op U))).toFunctor.map k)
                (Cat.Hom.inv_hom_id_toNatTrans_app
                  (F.mapId (.mk (op U))) x)
          _ = 𝟙 _ := (η.app (.mk (op U))).toFunctor.map_id _
      have hFy :
          (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).inv.toNatTrans.app y) ≫
              (η.app (.mk (op U))).toFunctor.map
                ((F.mapId (.mk (op U))).hom.toNatTrans.app y) =
            𝟙 _ := by
        calc
          _ = (η.app (.mk (op U))).toFunctor.map
              (𝟙 ((𝟭 (F.obj (.mk (op U)))).obj y)) := by
            simpa only [Functor.map_comp, Cat.Hom.id_toFunctor] using
              congrArg (fun k => (η.app (.mk (op U))).toFunctor.map k)
                (Cat.Hom.inv_hom_id_toNatTrans_app
                  (F.mapId (.mk (op U))) y)
          _ = 𝟙 _ := (η.app (.mk (op U))).toFunctor.map_id _
      simp only [← Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
        hFx, hFy, Category.id_comp]
      simp [Cat.Hom.id_toFunctor]
    simpa [hEq, Cat.Hom.id_toFunctor] using hcomp

theorem characterize_essentially_surjective_when_fully_faithful
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    [F.IsStack J] [G.IsStack J]
    (hη : FiberwiseFullyFaithful η) :
    FiberwiseEssentiallySurjective η ↔
      ∀ (U : C) (y : Fiber G U),
        ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
          CoveringFamily J f ∧
            ∀ i, ∃ x : Fiber F (X i),
              Nonempty
                ((G.map (f i).op.toLoc).toFunctor.obj y ≅
                  (η.app (.mk (op (X i)))).toFunctor.obj x) := by
  sorry

end Formalization.Books.Stacks.Unit01
