import Formalization.«Books.Stacks».Unit01.Setoids

/-!
# Stacks, Chapter 1, Section 7: the inertia stack
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory

universe t v' v u' u

structure RelativeInertiaMorphism {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} {η : FiberedMorphism F G} {U : C}
    (x y : RelativeInertiaObject η U) where
  hom : x.object ⟶ y.object
  commutes : x.automorphism ≫ hom = hom ≫ y.automorphism

def IsRelativeInertiaMorphism {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} {η : FiberedMorphism F G} {U : C}
    (x y : RelativeInertiaObject η U) (f : x.object ⟶ y.object) : Prop :=
  x.automorphism ≫ f = f ≫ y.automorphism

theorem relative_inertia_is_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hF : Stack F J) (hG : Stack G J) :
    ∃ (I : FiberedCategory C) (π : FiberedMorphism I F),
      StackInGroupoids I J ∧
        ∀ U : C, Nonempty (Fiber I U ≃ RelativeInertiaObject η U) := by
  sorry

theorem absolute_inertia_is_stack {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (F : FiberedCategory C)
    (hF : Stack F J) :
    ∃ (I : FiberedCategory C) (π : FiberedMorphism I F),
      StackInGroupoids I J ∧
        ∀ U : C, Nonempty
          (Fiber I U ≃ AbsoluteInertiaObject F U) := by
  sorry

theorem inertia_variants_are_stacks {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (hF : StackInGroupoids F J)
    (hG : StackInGroupoids G J) :
    ∃ I : FiberedCategory C, StackInGroupoids I J := by
  sorry

theorem inertia_characterizes_stack_in_setoids
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : FiberedCategory C} (hF : StackInGroupoids F J) :
    StackInSetoids F J ↔
      ∃ (I : FiberedCategory C) (π : FiberedMorphism I F),
        (∀ U : C, Nonempty
          (Fiber I U ≃ AbsoluteInertiaObject F U)) ∧
        FiberwiseEquivalence π := by
  sorry

end Formalization.«Books.Stacks».Unit01
