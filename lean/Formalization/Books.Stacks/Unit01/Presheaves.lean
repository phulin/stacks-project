import Formalization.«Books.Stacks».Unit01.Foundation

/-!
# Stacks, Chapter 1, Section 2: presheaves of morphisms
-/

namespace Formalization.«Books.Stacks».Unit01

/- The Mathlib descent presheaf is used as the canonical implementation. -/

open CategoryTheory
open Opposite

universe v' v u' u

theorem mor_presheaf_is_presheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    MorPresheaf F x y = F.presheafHom x y := rfl

theorem presheaf_mor_map_fibred_categories {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U) :
    Nonempty
      (F.presheafHom x y ⟶
        G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
          ((η.app (.mk (op U))).toFunctor.obj y)) := by
  sorry

theorem isom_presheaf_is_subpresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) (T : (Over C U)ᵒᵖ)
    (f : { f : (F.presheafHom x y).obj T // IsIso f }) : IsIso f.1 := f.2

structure TwoFiberProductPresentation {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) where
  apex : FiberedCategory (Over C U)
  isSetoid : FiberwiseSetoid apex
  presheaf : (Over C U)ᵒᵖ ⥤ Type v'
  presheafIso : presheaf ≅ IsomPresheaf F x y

theorem isom_as_two_fibre_product {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    Nonempty (TwoFiberProductPresentation F x y) := by
  sorry

end Formalization.«Books.Stacks».Unit01
