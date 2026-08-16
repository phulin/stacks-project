import Formalization.«Books.Stacks».Unit01.Foundation

/-!
# Stacks, Chapter 1, Section 2: presheaves of morphisms
-/

namespace Formalization.«Books.Stacks».Unit01

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
  sorry

theorem isom_presheaf_is_morphism_presheaf_of_groupoid
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    (hF : FiberwiseGroupoid F) {U : C} (x y : Fiber F U) :
    Nonempty (IsomPresheaf F x y ≅ F.presheafHom x y) := by
  sorry

end Formalization.«Books.Stacks».Unit01
