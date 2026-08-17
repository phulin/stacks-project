import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Whiskering

/-!
# Categories, Chapter 28: Formal properties

The source's functor categories and natural-transformation operations are the
canonical Mathlib interfaces.  In particular, `Functor.category` supplies the
category of functors and natural transformations, `whiskeringLeft` and
`whiskeringRight` supply the two functorial whiskering operations, and
`NatTrans.hcomp` supplies horizontal composition.  The declarations below
record the source-facing formulas and the product-category formulation.
-/

namespace Formalization.Books.Categories.Unit28

open CategoryTheory
open CategoryTheory.Functor

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

/-! ## Functor categories and whiskering -/

/- The imported `Functor.category` instance is the source's small category
   `Fun(A, B)`: its objects are functors and its morphisms are natural
   transformations.  Its categorical composition is vertical composition.
   The following interfaces record the source's component formulas and laws
   without introducing a second functor-category structure. -/

theorem vertical_composition_component
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G H : A ⥤ B} (t : F ⟶ G) (s : G ⟶ H) (X : A) :
    (t ≫ s).app X = t.app X ≫ s.app X :=
  NatTrans.comp_app t s X

theorem vertical_composition_associative
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G H K : A ⥤ B} (t : F ⟶ G) (s : G ⟶ H) (r : H ⟶ K) :
    (t ≫ s) ≫ r = t ≫ s ≫ r :=
  Category.assoc t s r

theorem vertical_composition_left_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B} (t : F ⟶ G) :
    (𝟙 F : F ⟶ F) ≫ t = t :=
  Category.id_comp t

theorem vertical_composition_right_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B} (t : F ⟶ G) :
    t ≫ (𝟙 G : G ⟶ G) = t :=
  Category.comp_id t

theorem functor_composition_associative
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {D : Type u₄} [Category.{v₄} D]
    (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) :
    (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  Functor.assoc F G H

theorem functor_composition_left_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) :
    𝟭 A ⋙ F = F :=
  Functor.id_comp F

theorem functor_composition_right_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    (F : A ⥤ B) :
    F ⋙ 𝟭 B = F :=
  Functor.comp_id F

/- The two definitions below are aliases for Mathlib's canonical functorial
   whiskering constructions. -/

/-- Postcomposition by `G`, carrying `t` to the source's `{}_G t`. -/
abbrev postcompositionFunctor
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (G : B ⥤ C) : (A ⥤ B) ⥤ (A ⥤ C) :=
  (Functor.whiskeringRight A B C).obj G

/-- Precomposition by `F`, carrying `s` to the source's `s_F`. -/
abbrev precompositionFunctor
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) : (B ⥤ C) ⥤ (A ⥤ C) :=
  (Functor.whiskeringLeft A B C).obj F

theorem postcompositionFunctor_obj
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (G : B ⥤ C) (F : A ⥤ B) :
    (postcompositionFunctor G).obj F = F ⋙ G :=
  rfl

theorem postcompositionFunctor_map
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (G : B ⥤ C) {F F' : A ⥤ B} (t : F ⟶ F') :
    (postcompositionFunctor G).map t = Functor.whiskerRight t G :=
  rfl

theorem precompositionFunctor_obj
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) (G : B ⥤ C) :
    (precompositionFunctor F).obj G = F ⋙ G :=
  rfl

theorem precompositionFunctor_map
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) {G G' : B ⥤ C} (s : G ⟶ G') :
    (precompositionFunctor F).map s = Functor.whiskerLeft F s :=
  rfl

theorem postwhisker_component
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} (G : B ⥤ C) (t : F ⟶ F') (X : A) :
    (Functor.whiskerRight t G).app X = G.map (t.app X) :=
  rfl

theorem prewhisker_component
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) {G G' : B ⥤ C} (s : G ⟶ G') (X : A) :
    (Functor.whiskerLeft F s).app X = s.app (F.obj X) :=
  rfl

theorem postwhisker_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F : A ⥤ B} (G : B ⥤ C) :
    Functor.whiskerRight (𝟙 F) G = 𝟙 (F ⋙ G) :=
  Functor.whiskerRight_id' G

theorem postwhisker_composition
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F G H : A ⥤ B} (t : F ⟶ G) (s : G ⟶ H) (K : B ⥤ C) :
    Functor.whiskerRight (t ≫ s) K =
      Functor.whiskerRight t K ≫ Functor.whiskerRight s K :=
  Functor.whiskerRight_comp t s K

theorem prewhisker_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) {G : B ⥤ C} :
    Functor.whiskerLeft F (𝟙 G) = 𝟙 (F ⋙ G) :=
  Functor.whiskerLeft_id' F

theorem prewhisker_composition
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    (F : A ⥤ B) {G H K : B ⥤ C} (s : G ⟶ H) (t : H ⟶ K) :
    Functor.whiskerLeft F (s ≫ t) =
      Functor.whiskerLeft F s ≫ Functor.whiskerLeft F t :=
  Functor.whiskerLeft_comp F s t

theorem postwhisker_identity_functor
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B} (t : F ⟶ G) :
    Functor.whiskerRight t (𝟭 B) = t := by
  rfl

theorem prewhisker_identity_functor
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B} (t : F ⟶ G) :
    Functor.whiskerLeft (𝟭 A) t = t := by
  rfl

/- Iterated whiskering is stated with Mathlib's explicit associators.  This is
   the source's strict equality after using the canonical associativity of
   functor composition. -/

theorem postwhisker_associativity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {D : Type u₄} [Category.{v₄} D]
    {F F' : A ⥤ B} (t : F ⟶ F') (G : B ⥤ C) (H : C ⥤ D) :
    Functor.whiskerRight (Functor.whiskerRight t G) H =
      (Functor.associator F G H).hom ≫
        Functor.whiskerRight t (G ⋙ H) ≫
          (Functor.associator F' G H).inv :=
  Functor.whiskerRight_twice G H t

theorem prewhisker_associativity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {D : Type u₄} [Category.{v₄} D]
    (F : A ⥤ B) (G : B ⥤ C) {H H' : C ⥤ D} (s : H ⟶ H') :
    Functor.whiskerLeft F (Functor.whiskerLeft G s) =
      (Functor.associator F G H).inv ≫
    Functor.whiskerLeft (F ⋙ G) s ≫
          (Functor.associator F G H').hom :=
  Functor.whiskerLeft_twice F G s

theorem postwhisker_prewhisker_associativity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {D : Type u₄} [Category.{v₄} D]
    (F : A ⥤ B) {G G' : B ⥤ C} (s : G ⟶ G') (H : C ⥤ D) :
    Functor.whiskerRight (Functor.whiskerLeft F s) H =
      (Functor.associator F G H).hom ≫
        Functor.whiskerLeft F (Functor.whiskerRight s H) ≫
          (Functor.associator F G' H).inv :=
  Functor.whiskerRight_left F s H

theorem whiskering_interchange
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G G' : B ⥤ C} (t : F ⟶ F') (s : G ⟶ G') :
    Functor.whiskerLeft F s ≫ Functor.whiskerRight t G' =
      Functor.whiskerRight t G ≫ Functor.whiskerLeft F' s :=
  Functor.whiskerLeft_comp_whiskerRight t s

/-! ## Horizontal composition -/

/-- The source's `s ⋆ t`, using Mathlib's canonical horizontal composition. -/
def horizontalComposition
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G G' : B ⥤ C}
    (s : G ⟶ G') (t : F ⟶ F') : F ⋙ G ⟶ F' ⋙ G' :=
  NatTrans.hcomp t s

theorem horizontalComposition_component
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G G' : B ⥤ C}
    (s : G ⟶ G') (t : F ⟶ F') (X : A) :
    (horizontalComposition s t).app X =
      s.app (F.obj X) ≫ G'.map (t.app X) :=
  rfl

theorem horizontalComposition_eq_postwhisker_comp_prewhisker
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G G' : B ⥤ C}
    (s : G ⟶ G') (t : F ⟶ F') :
    horizontalComposition s t =
      Functor.whiskerLeft F s ≫ Functor.whiskerRight t G' := by
  simpa [horizontalComposition] using
    (NatTrans.hcomp_eq_whiskerLeft_comp_whiskerRight t s)

theorem horizontalComposition_eq_prewhisker_comp_postwhisker
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G G' : B ⥤ C}
    (s : G ⟶ G') (t : F ⟶ F') :
    horizontalComposition s t =
      Functor.whiskerRight t G ≫ Functor.whiskerLeft F' s := by
  rw [horizontalComposition_eq_postwhisker_comp_prewhisker]
  exact Functor.whiskerLeft_comp_whiskerRight t s

theorem horizontalComposition_identity_outer
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' : A ⥤ B} {G : B ⥤ C} (t : F ⟶ F') :
    horizontalComposition (𝟙 G) t = Functor.whiskerRight t G := by
  simp [horizontalComposition]

theorem horizontalComposition_identity_inner
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F : A ⥤ B} {G G' : B ⥤ C} (s : G ⟶ G') :
    horizontalComposition s (𝟙 F) = Functor.whiskerLeft F s := by
  simp [horizontalComposition]

theorem horizontalComposition_associative
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {D : Type u₄} [Category.{v₄} D]
    {F F' : A ⥤ B} {G G' : B ⥤ C} {H H' : C ⥤ D}
    (r : H ⟶ H') (s : G ⟶ G') (t : F ⟶ F') :
    horizontalComposition r (horizontalComposition s t) =
      horizontalComposition (horizontalComposition r s) t := by
  ext X
  simp [horizontalComposition]

theorem horizontalComposition_left_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {F F' : A ⥤ B} (t : F ⟶ F') :
    horizontalComposition (𝟙 (𝟭 B)) t = t := by
  ext X
  simp [horizontalComposition]

theorem horizontalComposition_right_identity
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {G G' : A ⥤ B} (s : G ⟶ G') :
    horizontalComposition s (𝟙 (𝟭 A)) = s := by
  ext X
  simp [horizontalComposition]

theorem horizontalComposition_interchange
    {A : Type u₁} [Category.{v₁} A]
    {B : Type u₂} [Category.{v₂} B]
    {C : Type u₃} [Category.{v₃} C]
    {F F' F'' : A ⥤ B} {G G' G'' : B ⥤ C}
    (s : G ⟶ G') (s' : G' ⟶ G'')
    (t : F ⟶ F') (t' : F' ⟶ F'') :
    horizontalComposition (s ≫ s') (t ≫ t') =
      horizontalComposition s t ≫ horizontalComposition s' t' := by
  simpa [horizontalComposition] using NatTrans.exchange t t' s s'

/-! ## Composition as a functor from the product category -/

/-- The functor sending `(G, F)` to `F ⋙ G` and `(s, t)` to `s ⋆ t`. -/
def compositionFunctor
    (A : Type u₁) [Category.{v₁} A]
    (B : Type u₂) [Category.{v₂} B]
    (C : Type u₃) [Category.{v₃} C] :
    (B ⥤ C) × (A ⥤ B) ⥤ (A ⥤ C) where
  obj p := p.2 ⋙ p.1
  map {p q} f := horizontalComposition f.1 f.2
  map_id := by
    intro p
    ext X
    simp [horizontalComposition]
  map_comp := by
    intro p q r f g
    simpa [horizontalComposition] using NatTrans.exchange f.2 g.2 f.1 g.1

theorem compositionFunctor_obj
    (A : Type u₁) [Category.{v₁} A]
    (B : Type u₂) [Category.{v₂} B]
    (C : Type u₃) [Category.{v₃} C]
    (G : B ⥤ C) (F : A ⥤ B) :
    (compositionFunctor A B C).obj (G, F) = F ⋙ G :=
  rfl

theorem compositionFunctor_map
    (A : Type u₁) [Category.{v₁} A]
    (B : Type u₂) [Category.{v₂} B]
    (C : Type u₃) [Category.{v₃} C]
    {G G' : B ⥤ C} {F F' : A ⥤ B}
    (s : G ⟶ G') (t : F ⟶ F') :
    (compositionFunctor A B C).map (⟨s, t⟩ : (G, F) ⟶ (G', F')) =
      horizontalComposition s t :=
  rfl

end Formalization.Books.Categories.Unit28
