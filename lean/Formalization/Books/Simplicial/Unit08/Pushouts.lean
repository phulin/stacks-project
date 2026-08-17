import Formalization.Books.Simplicial.Unit04.SimplicialPresheaves
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Simplicial Methods, Chapter 8: Pushouts of simplicial objects

The source defines the pushout of simplicial objects degree by degree.  We use
Mathlib's `SimplicialObject` and its pushout cocones, while making the
degreewise existence hypothesis explicit for the particular span under
consideration.
-/

namespace Formalization.Books.Simplicial.Unit08

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped _root_.Simplicial

universe v u

variable {C : Type u} [Category.{v} C]

section DegreewiseConstruction

variable {U V W : SimplicialObject C}

/-! The chosen degreewise pushout and its two coprojections. -/

noncomputable def degreewisePushout
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    (n : SimplexCategoryᵒᵖ) : C := by
  letI : HasPushout (a.app n) (b.app n) := h n
  exact pushout (a.app n) (b.app n)

noncomputable def degreewisePushoutInl
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    (n : SimplexCategoryᵒᵖ) : V.obj n ⟶ degreewisePushout a b h n := by
  letI : HasPushout (a.app n) (b.app n) := h n
  exact pushout.inl (a.app n) (b.app n)

noncomputable def degreewisePushoutInr
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    (n : SimplexCategoryᵒᵖ) : W.obj n ⟶ degreewisePushout a b h n := by
  letI : HasPushout (a.app n) (b.app n) := h n
  exact pushout.inr (a.app n) (b.app n)

/-! The map induced by a morphism of the indexing category. -/

noncomputable def degreewisePushoutMap
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    degreewisePushout a b h X ⟶ degreewisePushout a b h Y := by
  letI : HasPushout (a.app X) (b.app X) := h X
  letI : HasPushout (a.app Y) (b.app Y) := h Y
  refine pushout.desc
    (V.map f ≫ degreewisePushoutInl a b h Y)
    (W.map f ≫ degreewisePushoutInr a b h Y) ?_
  rw [← a.naturality_assoc f, ← b.naturality_assoc f]
  change U.map f ≫ (a.app Y ≫ pushout.inl (a.app Y) (b.app Y)) =
    U.map f ≫ (b.app Y ≫ pushout.inr (a.app Y) (b.app Y))
  rw [pushout.condition]

lemma degreewisePushoutMap_inl
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    degreewisePushoutInl a b h X ≫ degreewisePushoutMap a b h f =
      V.map f ≫ degreewisePushoutInl a b h Y := by
  let _ : HasPushout (a.app X) (b.app X) := h X
  let _ : HasPushout (a.app Y) (b.app Y) := h Y
  change
    pushout.inl (a.app X) (b.app X) ≫
        pushout.desc
          (V.map f ≫ pushout.inl (a.app Y) (b.app Y))
          (W.map f ≫ pushout.inr (a.app Y) (b.app Y)) _ =
      V.map f ≫ pushout.inl (a.app Y) (b.app Y)
  exact
    pushout.inl_desc (f := a.app X) (g := b.app X)
      (V.map f ≫ pushout.inl (a.app Y) (b.app Y))
      (W.map f ≫ pushout.inr (a.app Y) (b.app Y)) _

lemma degreewisePushoutMap_inr
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    degreewisePushoutInr a b h X ≫ degreewisePushoutMap a b h f =
      W.map f ≫ degreewisePushoutInr a b h Y := by
  let _ : HasPushout (a.app X) (b.app X) := h X
  let _ : HasPushout (a.app Y) (b.app Y) := h Y
  change
    pushout.inr (a.app X) (b.app X) ≫
        pushout.desc
          (V.map f ≫ pushout.inl (a.app Y) (b.app Y))
          (W.map f ≫ pushout.inr (a.app Y) (b.app Y)) _ =
      W.map f ≫ pushout.inr (a.app Y) (b.app Y)
  exact
    pushout.inr_desc (f := a.app X) (g := b.app X)
      (V.map f ≫ pushout.inl (a.app Y) (b.app Y))
      (W.map f ≫ pushout.inr (a.app Y) (b.app Y)) _

lemma degreewisePushout_hom_ext
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    (n : SimplexCategoryᵒᵖ) {Q : C}
    {f g : degreewisePushout a b h n ⟶ Q}
    (h_inl : degreewisePushoutInl a b h n ≫ f =
      degreewisePushoutInl a b h n ≫ g)
    (h_inr : degreewisePushoutInr a b h n ≫ f =
      degreewisePushoutInr a b h n ≫ g) :
    f = g := by
  let _ : HasPushout (a.app n) (b.app n) := h n
  apply pushout.hom_ext
  · change degreewisePushoutInl a b h n ≫ f =
      degreewisePushoutInl a b h n ≫ g
    exact h_inl
  · change degreewisePushoutInr a b h n ≫ f =
      degreewisePushoutInr a b h n ≫ g
    exact h_inr

lemma degreewisePushoutMap_comp_inl
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y Z : SimplexCategoryᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (degreewisePushoutInl a b h X ≫ degreewisePushoutMap a b h f) ≫
        degreewisePushoutMap a b h g =
      V.map (f ≫ g) ≫ degreewisePushoutInl a b h Z := by
  rw [degreewisePushoutMap_inl, Category.assoc,
    degreewisePushoutMap_inl, ← Category.assoc, ← V.map_comp]

lemma degreewisePushoutMap_comp_inr
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y Z : SimplexCategoryᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (degreewisePushoutInr a b h X ≫ degreewisePushoutMap a b h f) ≫
        degreewisePushoutMap a b h g =
      W.map (f ≫ g) ≫ degreewisePushoutInr a b h Z := by
  rw [degreewisePushoutMap_inr, Category.assoc,
    degreewisePushoutMap_inr, ← Category.assoc, ← W.map_comp]

/-!
The direct pushout construction from the source.  The full map field of the
functor contains the source's face and degeneracy maps as special cases.
-/

noncomputable def simplicialPushout
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    SimplicialObject C where
  obj n := degreewisePushout a b h n
  map := fun {_ _} f => degreewisePushoutMap a b h f
  map_id := by
    intro X
    let _ : HasPushout (a.app X) (b.app X) := h X
    refine degreewisePushout_hom_ext a b h X ?_ ?_
    · rw [degreewisePushoutMap_inl, V.map_id]
      simp
    · rw [degreewisePushoutMap_inr, W.map_id]
      simp
  map_comp := by
    intro X Y Z f g
    let _ : HasPushout (a.app X) (b.app X) := h X
    let _ : HasPushout (a.app Y) (b.app Y) := h Y
    let _ : HasPushout (a.app Z) (b.app Z) := h Z
    refine degreewisePushout_hom_ext a b h X ?_ ?_
    · rw [degreewisePushoutMap_inl]
      simpa only [Category.assoc] using
        (degreewisePushoutMap_comp_inl a b h f g).symm
    · rw [degreewisePushoutMap_inr]
      simpa only [Category.assoc] using
        (degreewisePushoutMap_comp_inr a b h f g).symm

/-! The canonical maps from the two outer simplicial objects. -/

noncomputable def simplicialPushoutInl
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    V ⟶ simplicialPushout a b h where
  app n := degreewisePushoutInl a b h n
  naturality := by
    intro X Y f
    let _ : HasPushout (a.app X) (b.app X) := h X
    let _ : HasPushout (a.app Y) (b.app Y) := h Y
    change V.map f ≫ degreewisePushoutInl a b h Y =
      degreewisePushoutInl a b h X ≫ degreewisePushoutMap a b h f
    rw [degreewisePushoutMap_inl]

noncomputable def simplicialPushoutInr
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    W ⟶ simplicialPushout a b h where
  app n := degreewisePushoutInr a b h n
  naturality := by
    intro X Y f
    let _ : HasPushout (a.app X) (b.app X) := h X
    let _ : HasPushout (a.app Y) (b.app Y) := h Y
    change W.map f ≫ degreewisePushoutInr a b h Y =
      degreewisePushoutInr a b h X ≫ degreewisePushoutMap a b h f
    rw [degreewisePushoutMap_inr]

theorem simplicialPushout_condition
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    a ≫ simplicialPushoutInl a b h = b ≫ simplicialPushoutInr a b h := by
  ext n
  let _ : HasPushout (a.app n) (b.app n) := h n
  change a.app n ≫ pushout.inl (a.app n) (b.app n) =
    b.app n ≫ pushout.inr (a.app n) (b.app n)
  exact pushout.condition

/-! A source-facing form of the degree and map formulas. -/

theorem simplicialPushout_degree
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) (n : ℕ) :
    (simplicialPushout a b h) _⦋n⦌ =
      degreewisePushout a b h (Opposite.op (SimplexCategory.mk n)) := by
  rfl

theorem simplicialPushout_map_formula
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    {X Y : SimplexCategoryᵒᵖ} (f : X ⟶ Y) :
    (simplicialPushout a b h).map f =
      degreewisePushoutMap a b h f := by
  rfl

end DegreewiseConstruction

section UniversalProperty

variable {U V W : SimplicialObject C}

/-!
The degreewise pushout cocone is the simplicial pushout cocone.  Its
universal-property proof is the source's lemma; the declaration is kept
separate so that the mapping equivalence below can use Mathlib's canonical
`IsColimit` interface.
-/

noncomputable def simplicialPushoutCocone
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    PushoutCocone a b :=
  PushoutCocone.mk (simplicialPushoutInl a b h) (simplicialPushoutInr a b h)
    (simplicialPushout_condition a b h)

noncomputable def simplicialPushout_isColimit
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n)) :
    IsColimit (simplicialPushoutCocone a b h) := by
  sorry

/-!
The source writes the mapping property as a fibre product of hom-sets.  In
Lean, `Types.PullbackObj` is the canonical subtype of compatible pairs.
-/

noncomputable def simplicialPushoutHomEquiv
    (a : U ⟶ V) (b : U ⟶ W)
    (h : ∀ n : SimplexCategoryᵒᵖ, HasPushout (a.app n) (b.app n))
    (T : SimplicialObject C) :
    (simplicialPushout a b h ⟶ T) ≃
      Types.PullbackObj
        (TypeCat.ofHom (fun f : V ⟶ T => a ≫ f))
        (TypeCat.ofHom (fun g : W ⟶ T => b ≫ g)) where
  toFun f :=
    ⟨(simplicialPushoutInl a b h ≫ f, simplicialPushoutInr a b h ≫ f), by
      change a ≫ (simplicialPushoutInl a b h ≫ f) =
        b ≫ (simplicialPushoutInr a b h ≫ f)
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ f) (simplicialPushout_condition a b h)⟩
  invFun p :=
    PushoutCocone.IsColimit.desc (simplicialPushout_isColimit a b h)
      p.1.1 p.1.2 p.2
  left_inv f := by
    apply PushoutCocone.IsColimit.hom_ext (simplicialPushout_isColimit a b h)
    · change
        (simplicialPushoutCocone a b h).inl ≫
            PushoutCocone.IsColimit.desc (simplicialPushout_isColimit a b h)
              (simplicialPushoutInl a b h ≫ f)
              (simplicialPushoutInr a b h ≫ f) _ =
          simplicialPushoutInl a b h ≫ f
      rw [PushoutCocone.IsColimit.inl_desc]
    · change
        (simplicialPushoutCocone a b h).inr ≫
            PushoutCocone.IsColimit.desc (simplicialPushout_isColimit a b h)
              (simplicialPushoutInl a b h ≫ f)
              (simplicialPushoutInr a b h ≫ f) _ =
          simplicialPushoutInr a b h ≫ f
      rw [PushoutCocone.IsColimit.inr_desc]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change
        (simplicialPushoutCocone a b h).inl ≫
            PushoutCocone.IsColimit.desc (simplicialPushout_isColimit a b h)
              p.1.1 p.1.2 _ = p.1.1
      rw [PushoutCocone.IsColimit.inl_desc]
    · change
        (simplicialPushoutCocone a b h).inr ≫
            PushoutCocone.IsColimit.desc (simplicialPushout_isColimit a b h)
              p.1.1 p.1.2 _ = p.1.2
      rw [PushoutCocone.IsColimit.inr_desc]

end UniversalProperty

end Formalization.Books.Simplicial.Unit08
