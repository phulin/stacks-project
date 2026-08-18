import Formalization.Books.Stacks.Unit06.Setoids
import Formalization.Books.Stacks.Unit07.Foundation

/-!
# Stacks, Chapter 1, Section 7: the inertia stack
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open Opposite

universe t v' v u' u

structure RelativeInertiaMorphism {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} {η : FiberedMorphism F G} {U : C}
    (x y : RelativeInertiaObject η U) where
  hom : x.object ⟶ y.object
  commutes : x.automorphism.hom ≫ hom = hom ≫ y.automorphism.hom

instance relativeInertiaCategory {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} {η : FiberedMorphism F G} {U : C} :
    Category (RelativeInertiaObject η U) where
  Hom x y := RelativeInertiaMorphism x y
  id x := {
    hom := 𝟙 x.object
    commutes := by simp }
  comp f g := {
    hom := f.hom ≫ g.hom
    commutes := by
      rw [← Category.assoc, f.commutes, Category.assoc, g.commutes, ← Category.assoc] }

structure AbsoluteInertiaMorphism {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C}
    (x y : AbsoluteInertiaObject F U) where
  hom : x.object ⟶ y.object
  commutes : x.automorphism.hom ≫ hom = hom ≫ y.automorphism.hom

instance absoluteInertiaCategory {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C} :
    Category (AbsoluteInertiaObject F U) where
  Hom x y := AbsoluteInertiaMorphism x y
  id x := {
    hom := 𝟙 x.object
    commutes := by simp }
  comp f g := {
    hom := f.hom ≫ g.hom
    commutes := by
      rw [← Category.assoc, f.commutes, Category.assoc, g.commutes, ← Category.assoc] }

def relativeInertiaProjection {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} {η : FiberedMorphism F G} {U : C} :
    RelativeInertiaObject η U ⥤ Fiber F U where
  obj x := x.object
  map f := f.hom
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

def absoluteInertiaProjection {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {U : C} :
    AbsoluteInertiaObject F U ⥤ Fiber F U where
  obj x := x.object
  map f := f.hom
  map_id := by intro X; rfl
  map_comp := by intro X Y Z f g; rfl

structure RelativeInertiaStackData {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) where
  value : FiberedCategory C
  projection : FiberedMorphism value F
  isStack : Stack value J
  fibreEquivalence : ∀ U : C,
    ∃ e : Fiber value U ≌ RelativeInertiaObject η U,
      Nonempty
        (e.functor ⋙ relativeInertiaProjection ≅
          (projection.app (.mk (op U))).toFunctor)

structure AbsoluteInertiaPresentation {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) where
  value : FiberedCategory C
  projection : FiberedMorphism value F
  fibreEquivalence : ∀ U : C,
    ∃ e : Fiber value U ≌ AbsoluteInertiaObject F U,
      Nonempty
        (e.functor ⋙ absoluteInertiaProjection ≅
          (projection.app (.mk (op U))).toFunctor)

structure AbsoluteInertiaStackData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    extends AbsoluteInertiaPresentation F where
  isStack : Stack value J

theorem absolute_inertia_presentation_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Nonempty (AbsoluteInertiaPresentation F) := by
  sorry

theorem relative_inertia_is_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hF : Stack F J) (hG : Stack G J) :
    Nonempty (RelativeInertiaStackData η J) := by
  sorry

theorem absolute_inertia_is_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : FiberedCategory C)
    (hF : Stack F J) :
    Nonempty (AbsoluteInertiaStackData F J) := by
  sorry

theorem inertia_variants_are_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hF : StackInGroupoids F J)
    (hG : StackInGroupoids G J) :
    ∃ (R : RelativeInertiaStackData η J)
      (A : AbsoluteInertiaStackData F J),
      StackInGroupoids R.value J ∧ StackInGroupoids A.value J := by
  sorry

theorem inertia_variants_of_setoid_stacks_are_setoid_stacks
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hF : StackInSetoids F J)
    (hG : StackInSetoids G J) :
    ∃ (R : RelativeInertiaStackData η J)
      (A : AbsoluteInertiaStackData F J),
      StackInSetoids R.value J ∧ StackInSetoids A.value J := by
  sorry

theorem inertia_characterizes_stack_in_setoids
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : FiberedCategory C} (hF : StackInGroupoids F J) :
    StackInSetoids F J ↔
      ∃ (A : AbsoluteInertiaPresentation F),
        StackInGroupoids A.value J ∧ FiberwiseEquivalence A.projection := by
  sorry

end Formalization.Books.Stacks.Unit01
