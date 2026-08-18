import Formalization.Books.Stacks.Unit03.Foundation
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Stacks, Unit 4: stack and two-fibre-product interfaces

These declarations retain their established namespace for downstream compatibility,
but are owned by the source unit corresponding to this file path.
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Formalization.Books.Categories.Unit31
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

variable {C : Type u} [Category.{v} C]

structure Substack (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  inclusion : FiberedMorphism value F
  fullyFaithful : FiberwiseFullyFaithful inclusion
  stableUnderPullback : ∀ {U V : C} (f : V ⟶ U) (x : Fiber value U),
    ∃ y : Fiber value V,
      Nonempty (y ≅ (value.map f.op.toLoc).toFunctor.obj x)
  locallyEssentiallyInImage : ∀ (U : C) (x : Fiber F U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ y : Fiber value (X i),
          Nonempty ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (inclusion.app (.mk (op (X i)))).toFunctor.obj y)

def IsTwoPullbackCone {F G H A : FiberedCategory C}
    (f : FiberedMorphism F H) (g : FiberedMorphism G H)
    (left : FiberedMorphism A F) (right : FiberedMorphism A G)
    (commutes : left ≫ f ≅ right ≫ g) : Prop :=
  ∀ (Q : FiberedCategory C) (a : FiberedMorphism Q F)
      (b : FiberedMorphism Q G) (α : a ≫ f ≅ b ≫ g),
    ∃ (u : FiberedMorphism Q A) (lam : u ≫ left ≅ a)
      (rho : u ≫ right ≅ b),
      (Bicategory.whiskerRight lam.hom f) ≫ α.hom =
          (Bicategory.associator u left f).hom ≫
            Bicategory.whiskerLeft u commutes.hom ≫
              (Bicategory.associator u right g).inv ≫
                (Bicategory.whiskerRight rho.hom g) ∧
        ∀ (v : FiberedMorphism Q A) (lam' : v ≫ left ≅ a)
          (rho' : v ≫ right ≅ b),
          (Bicategory.whiskerRight lam'.hom f) ≫ α.hom =
              (Bicategory.associator v left f).hom ≫
                Bicategory.whiskerLeft v commutes.hom ≫
                  (Bicategory.associator v right g).inv ≫
                    (Bicategory.whiskerRight rho'.hom g) →
            ∃! β : u ⟶ v,
              (Bicategory.whiskerRight β left) ≫ lam'.hom = lam.hom ∧
                (Bicategory.whiskerRight β right) ≫ rho'.hom = rho.hom

structure TwoFiberProductCone (F G H : FiberedCategory C)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) where
  apex : FiberedCategory C
  left : FiberedMorphism apex F
  right : FiberedMorphism apex G
  commutes : left ≫ f ≅ right ≫ g
  isTwoPullback : IsTwoPullbackCone f g left right commutes

/-! ### The canonical pointwise two-fibre product

The value of the two-fibre product over `U` is the iso-comma category of the
two component functors `f.app U` and `g.app U`.  The map on a morphism `q` of
the base is the iso-comma map induced by the three reindexing functors and the
two strong-transformation coherence isomorphisms.  The coherence fields of
the resulting pseudofunctor, and its bicategorical universal property, are
recorded below so that later stack arguments use one canonical cone.
-/

noncomputable def pointwiseTwoFiberProductReindex
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) {U V : LocallyDiscrete Cᵒᵖ} (q : U ⟶ V) :
    IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor) ⥤
      IsoComma ((f.app V).toFunctor) ((g.app V).toFunctor) :=
  isoCommaMap
    ((f.app V).toFunctor) ((g.app V).toFunctor)
    ((f.app U).toFunctor) ((g.app U).toFunctor)
    ((F.map q).toFunctor) ((G.map q).toFunctor) ((H.map q).toFunctor)
    (Cat.Hom.toNatIso (g.naturality q))
    (Cat.Hom.toNatIso (f.naturality q).symm)

private theorem pointwiseTwoFiberProductMapId_hom
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) (U : Cᵒᵖ)
    (ξ : IsoComma ((f.app (.mk U)).toFunctor) ((g.app (.mk U)).toFunctor)) :
    (f.app (.mk U)).toFunctor.map
          ((Cat.Hom.toNatIso (F.mapId (.mk U))).app ξ.obj.left).hom ≫
        ((𝟭 (Cat.of (IsoComma (f.app (.mk U)).toFunctor
          (g.app (.mk U)).toFunctor))).obj ξ).obj.hom =
      ((pointwiseTwoFiberProductReindex f g (Discrete.mk (𝟙 U))).obj ξ).obj.hom ≫
        (g.app (.mk U)).toFunctor.map
          ((Cat.Hom.toNatIso (G.mapId (.mk U))).app ξ.obj.right).hom := by
  dsimp [pointwiseTwoFiberProductReindex, isoCommaMap]
  simp only [Cat.Hom.toNatIso, Iso.symm_hom, Iso.symm_inv]
  change
    (f.app (.mk U)).toFunctor.map
        ((F.mapId (.mk U)).hom.toNatTrans.app ξ.obj.left) ≫
        ((𝟭 (IsoComma (f.app (.mk U)).toFunctor
            (g.app (.mk U)).toFunctor)).obj ξ).obj.hom =
      ((f.naturality (𝟙 (.mk U))).hom.toNatTrans.app ξ.obj.left ≫
          (H.map (𝟙 (.mk U))).toFunctor.map ξ.obj.hom ≫
            (g.naturality (𝟙 (.mk U))).inv.toNatTrans.app ξ.obj.right) ≫
        (g.app (.mk U)).toFunctor.map
          ((G.mapId (.mk U)).hom.toNatTrans.app ξ.obj.right)
  simp [Pseudofunctor.StrongTrans.naturality_id_hom,
    Pseudofunctor.StrongTrans.naturality_id_inv,
    ← Functor.map_comp, Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app]

private noncomputable def pointwiseTwoFiberProductMapId
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) (U : Cᵒᵖ) :
    (pointwiseTwoFiberProductReindex f g (Discrete.mk (𝟙 U))).toCatHom ≅
      𝟙 (Cat.of (IsoComma ((f.app (.mk U)).toFunctor)
        ((g.app (.mk U)).toFunctor))) := by
  refine Cat.Hom.isoMk (NatIso.ofComponents (fun ξ => ?_) ?_)
  · let eF := Cat.Hom.toNatIso (F.mapId (.mk U))
    let eG := Cat.Hom.toNatIso (G.mapId (.mk U))
    apply ObjectProperty.isoMk
    exact Comma.isoMk (l := eF.app ξ.obj.left) (r := eG.app ξ.obj.right)
      (pointwiseTwoFiberProductMapId_hom f g U ξ)
  · intro ξ ζ h
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact (Cat.Hom.toNatIso (F.mapId (.mk U))).hom.naturality h.hom.left
    · exact (Cat.Hom.toNatIso (G.mapId (.mk U))).hom.naturality h.hom.right

set_option linter.unnecessarySimpa false in
private theorem pointwiseTwoFiberProductMapComp_hom
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) {U V W : Cᵒᵖ} (q : U ⟶ V) (r : V ⟶ W)
    (ξ : IsoComma ((f.app (.mk U)).toFunctor) ((g.app (.mk U)).toFunctor)) :
    (f.app (.mk W)).toFunctor.map
          ((Cat.Hom.toNatIso
            (F.mapComp (Discrete.mk q) (Discrete.mk r))).app ξ.obj.left).hom ≫
        (((pointwiseTwoFiberProductReindex f g (Discrete.mk q)).toCatHom.toFunctor ⋙
          (pointwiseTwoFiberProductReindex f g (Discrete.mk r)).toCatHom.toFunctor).obj
            ξ).obj.hom =
      ((pointwiseTwoFiberProductReindex f g (Discrete.mk (q ≫ r))).obj ξ).obj.hom ≫
        (g.app (.mk W)).toFunctor.map
          ((Cat.Hom.toNatIso
            (G.mapComp (Discrete.mk q) (Discrete.mk r))).app ξ.obj.right).hom := by
  dsimp [Functor.comp, pointwiseTwoFiberProductReindex, isoCommaMap]
  simp only [Cat.Hom.toNatIso, Iso.symm_hom, Iso.symm_inv]
  have hfcomp :=
    Pseudofunctor.StrongTrans.naturality_comp_hom_app f
      (Discrete.mk q) (Discrete.mk r) ξ.obj.left
  have hgcomp :=
    Pseudofunctor.StrongTrans.naturality_comp_inv_app g
      (Discrete.mk q) (Discrete.mk r) ξ.obj.right
  change
    (f.naturality (Discrete.mk (q ≫ r))).hom.toNatTrans.app ξ.obj.left = _
      at hfcomp
  change
    (g.naturality (Discrete.mk (q ≫ r))).inv.toNatTrans.app ξ.obj.right = _
      at hgcomp
  rw [hfcomp, hgcomp]
  have hH :
      (H.mapComp (Discrete.mk q) (Discrete.mk r)).inv.toNatTrans.app
            ((f.app (.mk U)).toFunctor.obj ξ.obj.left) ≫
          (H.map (Discrete.mk (q ≫ r))).toFunctor.map ξ.obj.hom ≫
        (H.mapComp (Discrete.mk q) (Discrete.mk r)).hom.toNatTrans.app
          ((g.app (.mk U)).toFunctor.obj ξ.obj.right) =
      (H.map (Discrete.mk r)).toFunctor.map
        ((H.map (Discrete.mk q)).toFunctor.map ξ.obj.hom) := by
    have hH' := H.mapComp'_naturality_1 (Discrete.mk q) (Discrete.mk r)
      (Discrete.mk q ≫ Discrete.mk r) rfl ξ.obj.hom
    rw [Pseudofunctor.mapComp'_eq_mapComp] at hH'
    exact hH'
  have hH_full := congrArg (fun k =>
    ((f.app (.mk W)).toFunctor.map
          ((F.mapComp (Discrete.mk q) (Discrete.mk r)).hom.toNatTrans.app
            ξ.obj.left) ≫
        (f.naturality (Discrete.mk r)).hom.toNatTrans.app
          ((F.map (Discrete.mk q)).toFunctor.obj ξ.obj.left) ≫
        (H.map (Discrete.mk r)).toFunctor.map
          ((f.naturality (Discrete.mk q)).hom.toNatTrans.app ξ.obj.left)) ≫
      k ≫
        ((H.map (Discrete.mk r)).toFunctor.map
              ((g.naturality (Discrete.mk q)).inv.toNatTrans.app ξ.obj.right) ≫
          (g.naturality (Discrete.mk r)).inv.toNatTrans.app
            ((G.map (Discrete.mk q)).toFunctor.obj ξ.obj.right) ≫
          (g.app (.mk W)).toFunctor.map
            ((G.mapComp (Discrete.mk q) (Discrete.mk r)).inv.toNatTrans.app
              ξ.obj.right) ≫
          (g.app (.mk W)).toFunctor.map
            ((G.mapComp (Discrete.mk q) (Discrete.mk r)).hom.toNatTrans.app
              ξ.obj.right))) hH
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app] at hH_full ⊢
  simpa using hH_full.symm

private noncomputable def pointwiseTwoFiberProductMapComp
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) {U V W : Cᵒᵖ} (q : U ⟶ V) (r : V ⟶ W) :
    (pointwiseTwoFiberProductReindex f g (Discrete.mk (q ≫ r))).toCatHom ≅
      (pointwiseTwoFiberProductReindex f g (Discrete.mk q)).toCatHom ≫
        (pointwiseTwoFiberProductReindex f g (Discrete.mk r)).toCatHom := by
  refine Cat.Hom.isoMk (NatIso.ofComponents (fun ξ => ?_) ?_)
  · apply ObjectProperty.isoMk
    exact Comma.isoMk
      (l := (Cat.Hom.toNatIso
        (F.mapComp (Discrete.mk q) (Discrete.mk r))).app ξ.obj.left)
      (r := (Cat.Hom.toNatIso
        (G.mapComp (Discrete.mk q) (Discrete.mk r))).app ξ.obj.right)
      (pointwiseTwoFiberProductMapComp_hom f g q r ξ)
  · intro ξ ζ h
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · exact (Cat.Hom.toNatIso
        (F.mapComp (Discrete.mk q) (Discrete.mk r))).hom.naturality h.hom.left
    · exact (Cat.Hom.toNatIso
        (G.mapComp (Discrete.mk q) (Discrete.mk r))).hom.naturality h.hom.right

noncomputable def pointwiseTwoFiberProductApex
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) : FiberedCategory C :=
  LocallyDiscrete.mkPseudofunctor
    (fun U : Cᵒᵖ =>
      Cat.of (IsoComma ((f.app (.mk U)).toFunctor) ((g.app (.mk U)).toFunctor)))
    (fun {U V : Cᵒᵖ} q =>
      (pointwiseTwoFiberProductReindex f g (Discrete.mk q)).toCatHom)
    (pointwiseTwoFiberProductMapId f g)
    (pointwiseTwoFiberProductMapComp f g)
    (fun {U V W X : Cᵒᵖ} q r s => by
      sorry)
    (fun {U V : Cᵒᵖ} q => by
      sorry)
    (fun {U V : Cᵒᵖ} q => by
      sorry)

noncomputable def pointwiseTwoFiberProductLeft
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    FiberedMorphism (pointwiseTwoFiberProductApex f g) F := by
  exact
    { app := fun U => by
        change Cat.of (IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)) ⟶ F.obj U
        exact (isoCommaLeft ((f.app U).toFunctor) ((g.app U).toFunctor)).toCatHom
      naturality := by
        intro U V q
        sorry
      naturality_naturality := by
        intro U V q r h
        sorry
      naturality_id := by
        intro U
        sorry
      naturality_comp := by
        intro U V W q r
        sorry }

noncomputable def pointwiseTwoFiberProductRight
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    FiberedMorphism (pointwiseTwoFiberProductApex f g) G := by
  exact
    { app := fun U => by
        change Cat.of (IsoComma ((f.app U).toFunctor) ((g.app U).toFunctor)) ⟶ G.obj U
        exact (isoCommaRight ((f.app U).toFunctor) ((g.app U).toFunctor)).toCatHom
      naturality := by
        intro U V q
        sorry
      naturality_naturality := by
        intro U V q r h
        sorry
      naturality_id := by
        intro U
        sorry
      naturality_comp := by
        intro U V W q r
        sorry }

noncomputable def pointwiseTwoFiberProductCommutes
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    pointwiseTwoFiberProductLeft f g ≫ f ≅
      pointwiseTwoFiberProductRight f g ≫ g := by
  refine Pseudofunctor.StrongTrans.isoMk (fun U => ?_) ?_
  · dsimp [pointwiseTwoFiberProductLeft, pointwiseTwoFiberProductRight,
      Pseudofunctor.StrongTrans.vcomp]
    exact Cat.Hom.isoMk
      (isoCommaComparisonIso ((f.app U).toFunctor) ((g.app U).toFunctor))
  · intro U V q
    sorry

noncomputable def pointwiseTwoFiberProductCone
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) : TwoFiberProductCone F G H f g :=
  { apex := pointwiseTwoFiberProductApex f g
    left := pointwiseTwoFiberProductLeft f g
    right := pointwiseTwoFiberProductRight f g
    commutes := pointwiseTwoFiberProductCommutes f g
    isTwoPullback := by
      sorry }

theorem pointwiseTwoFiberProductCone_isTwoPullback
    {C : Type u} [Category.{v} C]
    {F G H : FiberedCategory C} (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    IsTwoPullbackCone f g
      (pointwiseTwoFiberProductCone f g).left
      (pointwiseTwoFiberProductCone f g).right
      (pointwiseTwoFiberProductCone f g).commutes :=
  (pointwiseTwoFiberProductCone f g).isTwoPullback

theorem pointwiseTwoFiberProductCone_apex_is_stack
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    Stack (pointwiseTwoFiberProductCone f g).apex J := by
  sorry

theorem pointwise_two_fibre_product_of_stacks
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G H : FiberedCategory C}
    (hF : Stack F J) (hG : Stack G J) (hH : Stack H J)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, Stack P.apex J := by
  refine ⟨pointwiseTwoFiberProductCone f g, ?_⟩
  exact pointwiseTwoFiberProductCone_apex_is_stack J hF hG hH f g


end Formalization.Books.Stacks.Unit01
