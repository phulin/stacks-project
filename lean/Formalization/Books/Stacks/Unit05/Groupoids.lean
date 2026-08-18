import Formalization.Books.Stacks.Unit04.Stacks

/-!
# Stacks, Chapter 1, Section 5: stacks in groupoids
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v' v u' u

def StackInGroupoids {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseGroupoid F ∧ Stack F J

structure GroupoidificationData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism value F
  isStackInGroupoids : StackInGroupoids value J

structure StackInGroupoidsObject (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  value : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  isStackInGroupoids : StackInGroupoids value J

theorem stack_in_groupoids_iff {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C} :
    StackInGroupoids F J ↔ FiberwiseGroupoid F ∧ Stack F J := Iff.rfl

theorem stack_groupoidification {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    (hF : Stack F J) : Nonempty (GroupoidificationData F J) := by
  sorry

theorem equivalent_stacks_in_groupoids_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    StackInGroupoids F J ↔ StackInGroupoids G J := by
  constructor
  · rintro ⟨hFgroup, hFstack⟩
    refine ⟨?_, (equivalent_fibred_categories_preserve_stack η hη).mp hFstack⟩
    intro U
    rcases hη.1 U with ⟨hηff⟩
    let hηess := hη.2 U
    constructor
    intro X Y f
    let eX :=
      @Functor.objObjPreimageIso _ _ _ _ (η.app (.mk (op U))).toFunctor hηess X
    let eY :=
      @Functor.objObjPreimageIso _ _ _ _ (η.app (.mk (op U))).toFunctor hηess Y
    let a := hηff.preimage (eX.hom ≫ f ≫ eY.inv)
    have ha : (η.app (.mk (op U))).toFunctor.map a =
        eX.hom ≫ f ≫ eY.inv := hηff.map_preimage _
    have hf : f = eX.inv ≫
        (η.app (.mk (op U))).toFunctor.map a ≫ eY.hom := by
      rw [ha]
      simp
    let haIso : IsIso a := IsGroupoid.all_isIso (self := hFgroup U) a
    let hmapIso : IsIso ((η.app (.mk (op U))).toFunctor.map a) :=
      @Functor.map_isIso _ _ _ _ _ _ (η.app (.mk (op U))).toFunctor a haIso
    rw [hf]
    exact IsIso.comp_isIso'
      eX.isIso_inv (IsIso.comp_isIso' hmapIso eY.isIso_hom)
  · rintro ⟨hGgroup, hGstack⟩
    refine ⟨?_, (equivalent_fibred_categories_preserve_stack η hη).mpr hGstack⟩
    intro U
    rcases hη.1 U with ⟨hηff⟩
    constructor
    intro X Y f
    let hmap : IsIso ((η.app (.mk (op U))).toFunctor.map f) :=
      IsGroupoid.all_isIso (self := hGgroup U) _
    exact @Functor.FullyFaithful.isIso_of_isIso_map _ _ _ _ _ hηff _ _ f hmap

def IsGroupoidTwoMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {X Y : StackInGroupoidsObject C J}
    (f g : FiberedMorphism X.value Y.value) : Prop :=
  Nonempty (f ⟶ g)

theorem two_fibre_product_of_stacks_in_groupoids
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {F G H : FiberedCategory C}
    (hF : StackInGroupoids F J) (hG : StackInGroupoids G J)
    (hH : StackInGroupoids H J) (f : FiberedMorphism F H)
    (g : FiberedMorphism G H) :
    ∃ P : TwoFiberProductCone F G H f g, StackInGroupoids P.apex J := by
  sorry

end Formalization.Books.Stacks.Unit01
