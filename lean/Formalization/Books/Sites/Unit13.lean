import Formalization.Books.Sites.Unit10.Sheafification
import Formalization.Books.Sites.Unit05.Functoriality
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Sites and Sheaves, Chapter 13: Continuous functors

This file formalizes the section `Continuous functors`.  The canonical
presheaf restriction and left Kan extension from Chapter 5 are reused.  A
continuous functor is stated using the indexed-family presentation of the
covering condition, while its pullback comparison maps use the chosen
categorical pullbacks.
-/

namespace Formalization.Books.Sites.Unit13

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presieve
open Formalization.Books.Sites.Unit02
open Formalization.Books.Sites.Unit05
open Formalization.Books.Sites.Unit06
open Formalization.Books.Sites.Unit07
open Formalization.Books.Sites.Unit08
open Formalization.Books.Sites.Unit10
open Opposite

universe u v w

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable [HasPullbacks C] [HasPullbacks D]

/-! ## Continuous functors -/

/- The comparison map is canonical once pullbacks in the source and target
are fixed. -/
noncomputable def pullbackComparison (u : C ⥤ D) {T V W : C}
    (g : T ⟶ V) (f : W ⟶ V) :
    u.obj (pullback g f) ⟶ pullback (u.map g) (u.map f) :=
  pullback.lift (u.map (pullback.fst g f)) (u.map (pullback.snd g f)) (by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition])

theorem pullbackComparison_fst (u : C ⥤ D) {T V W : C}
    (g : T ⟶ V) (f : W ⟶ V) :
    pullbackComparison u g f ≫ pullback.fst (u.map g) (u.map f) =
      u.map (pullback.fst g f) := by
  apply pullback.lift_fst

theorem pullbackComparison_snd (u : C ⥤ D) {T V W : C}
    (g : T ⟶ V) (f : W ⟶ V) :
    pullbackComparison u g f ≫ pullback.snd (u.map g) (u.map f) =
      u.map (pullback.snd g f) := by
  apply pullback.lift_snd

def Continuous (J : Site C) (K : Site D) (u : C ⥤ D) : Prop :=
  ∀ {ι : Type w} {V : C} (W : ι → C) (f : ∀ i, W i ⟶ V),
    familyOfArrows W f ∈ coverings J V →
      familyOfArrows (fun i => u.obj (W i)) (fun i => u.map (f i)) ∈
          coverings K (u.obj V) ∧
        ∀ {T : C} (g : T ⟶ V) (i : ι),
          IsIso (pullbackComparison u g (f i))

/-! The source's restriction notation `u^p` is Chapter 5's canonical
precomposition functor. -/

@[simp] theorem pullbackPresheaf_obj (u : C ⥤ D) (F : Presheaf D) (V : C) :
    (pullbackPresheaf u F).obj (op V) = F.obj (op (u.obj V)) := rfl

theorem pullbackPresheaf_isSheaf (J : Site C) (K : Site D) (u : C ⥤ D)
    (hu : Continuous J K u) (F : Presheaf D)
    (hF : Presheaf.IsSheaf K.toGrothendieck F) :
    Presheaf.IsSheaf J.toGrothendieck (pullbackPresheaf u F) := by
  sorry

/-! ## Restriction and pushforward on sheaves -/

noncomputable def pullbackSheafFunctor (J : Site C) (K : Site D)
    (u : C ⥤ D) (hu : Continuous J K u) :
    Sheaf K.toGrothendieck (Type v) ⥤ Sheaf J.toGrothendieck (Type v) :=
  { obj := fun F =>
      ⟨pullbackPresheaf u F.obj,
        pullbackPresheaf_isSheaf J K u hu F.obj F.property⟩
    map := fun f => ⟨(pullbackPresheafFunctor u).map f.hom⟩
    map_id := by
      intro F
      rfl
    map_comp := by
      intro F G H f g
      rfl }

noncomputable def pushforwardSheafFunctor (J : Site C) (K : Site D)
    (u : C ⥤ D)
    [hC₁ : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C)
      (S : CoveringCategory J X), HasMultiequalizer (S.index P)]
    [hC₂ : ∀ X : C, HasColimitsOfShape (CoveringCategory J X)ᵒᵖ (Type v)]
    [hD₁ : ∀ (P : Dᵒᵖ ⥤ Type v) (X : D)
      (S : CoveringCategory K X), HasMultiequalizer (S.index P)]
    [hD₂ : ∀ X : D, HasColimitsOfShape (CoveringCategory K X)ᵒᵖ (Type v)]
    [h : HasLeftPushforward u] :
    Sheaf J.toGrothendieck (Type v) ⥤ Sheaf K.toGrothendieck (Type v) :=
  sheafToPresheaf J.toGrothendieck (Type v) ⋙
    pushforwardPresheafFunctor u ⋙
      (associatedSheafFunctor K :
        (Dᵒᵖ ⥤ Type v) ⥤ Sheaf K.toGrothendieck (Type v))

noncomputable def pushforwardSheaf_pullbackSheaf_adjunction
    (J : Site C) (K : Site D) (u : C ⥤ D) (hu : Continuous J K u)
    [hC₁ : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C)
      (S : CoveringCategory J X), HasMultiequalizer (S.index P)]
    [hC₂ : ∀ X : C, HasColimitsOfShape (CoveringCategory J X)ᵒᵖ (Type v)]
    [hD₁ : ∀ (P : Dᵒᵖ ⥤ Type v) (X : D)
      (S : CoveringCategory K X), HasMultiequalizer (S.index P)]
    [hD₂ : ∀ X : D, HasColimitsOfShape (CoveringCategory K X)ᵒᵖ (Type v)]
    [h : HasLeftPushforward u] :
    pushforwardSheafFunctor J K u ⊣ pullbackSheafFunctor J K u hu := by
  sorry

theorem pushforward_sheafification_commutes (J : Site C) (K : Site D)
    (u : C ⥤ D) (G : Presheaf C)
    [hC₁ : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C)
      (S : CoveringCategory J X), HasMultiequalizer (S.index P)]
    [hC₂ : ∀ X : C, HasColimitsOfShape (CoveringCategory J X)ᵒᵖ (Type v)]
    [hD₁ : ∀ (P : Dᵒᵖ ⥤ Type v) (X : D)
      (S : CoveringCategory K X), HasMultiequalizer (S.index P)]
    [hD₂ : ∀ X : D, HasColimitsOfShape (CoveringCategory K X)ᵒᵖ (Type v)]
    [h : HasLeftPushforward u] :
    associatedSheafPresheaf K (pushforwardPresheaf u G) =
      associatedSheafPresheaf K
        (pushforwardPresheaf u (associatedSheafPresheaf J G)) := by
  sorry

noncomputable def pullback_representable_sheaf_iso (J : Site C) (K : Site D)
    (u : C ⥤ D) (hu : Continuous J K u) (U : C)
    [hC₁ : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C)
      (S : CoveringCategory J X), HasMultiequalizer (S.index P)]
    [hC₂ : ∀ X : C, HasColimitsOfShape (CoveringCategory J X)ᵒᵖ (Type v)]
    [hD₁ : ∀ (P : Dᵒᵖ ⥤ Type v) (X : D)
      (S : CoveringCategory K X), HasMultiequalizer (S.index P)]
    [hD₂ : ∀ X : D, HasColimitsOfShape (CoveringCategory K X)ᵒᵖ (Type v)]
    [h : HasLeftPushforward u] :
    (pushforwardSheafFunctor J K u).obj
        ((associatedSheafFunctor J).obj (representablePresheaf U)) ≅
      (associatedSheafFunctor K).obj (representablePresheaf (u.obj U)) := by
  sorry

/-! ## Quasi-continuity -/

def mapIndexedFamily (u : C ⥤ D) {V : C}
    (𝒱 : IndexedFamily.{u, v, w} C V) : IndexedFamily.{u, v, w} D (u.obj V) :=
  { index := 𝒱.index
    domain := fun i => u.obj (𝒱.domain i)
    map := fun i => u.map (𝒱.map i) }

def QuasiContinuous (J : Site C) (K : Site D) (u : C ⥤ D) : Prop :=
  ∀ {V : C} (𝒱 : IndexedFamily.{u, v, w} C V),
    𝒱.presieve ∈ coverings J V →
      ∃ 𝒰 : IndexedFamily.{u, v, w} D (u.obj V),
        𝒰.presieve ∈ coverings K (u.obj V) ∧
          TautologicallyEquivalent (mapIndexedFamily u 𝒱) 𝒰 ∧
            ∀ {T : C} (g : T ⟶ V) (i : 𝒱.index),
              IsIso (pullbackComparison u g (𝒱.map i))

theorem continuous_quasiContinuous (J : Site C) (K : Site D)
    (u : C ⥤ D) (hu : Continuous J K u) : QuasiContinuous J K u := by
  sorry

theorem quasiContinuous_pullbackPresheaf_isSheaf (J : Site C) (K : Site D)
    (u : C ⥤ D) (hu : QuasiContinuous J K u) (F : Presheaf D)
    (hF : Presheaf.IsSheaf K.toGrothendieck F) :
    Presheaf.IsSheaf J.toGrothendieck (pullbackPresheaf u F) := by
  sorry

noncomputable def quasiPullbackSheafFunctor (J : Site C) (K : Site D)
    (u : C ⥤ D) (hu : QuasiContinuous J K u) :
    Sheaf K.toGrothendieck (Type v) ⥤ Sheaf J.toGrothendieck (Type v) :=
  { obj := fun F =>
      ⟨pullbackPresheaf u F.obj,
        quasiContinuous_pullbackPresheaf_isSheaf J K u hu F.obj F.property⟩
    map := fun f => ⟨(pullbackPresheafFunctor u).map f.hom⟩
    map_id := by
      intro F
      rfl
    map_comp := by
      intro F G H f g
      rfl }

noncomputable def quasiContinuous_pushforwardSheaf_pullbackSheaf_adjunction
    (J : Site C) (K : Site D) (u : C ⥤ D) (hu : QuasiContinuous J K u)
    [hC₁ : ∀ (P : Cᵒᵖ ⥤ Type v) (X : C)
      (S : CoveringCategory J X), HasMultiequalizer (S.index P)]
    [hC₂ : ∀ X : C, HasColimitsOfShape (CoveringCategory J X)ᵒᵖ (Type v)]
    [hD₁ : ∀ (P : Dᵒᵖ ⥤ Type v) (X : D)
      (S : CoveringCategory K X), HasMultiequalizer (S.index P)]
    [hD₂ : ∀ X : D, HasColimitsOfShape (CoveringCategory K X)ᵒᵖ (Type v)]
    [h : HasLeftPushforward u] :
    pushforwardSheafFunctor J K u ⊣ quasiPullbackSheafFunctor J K u hu := by
  sorry

end Formalization.Books.Sites.Unit13
