import Formalization.«Books.Stacks».Unit01.StackificationGroupoids
import Mathlib.CategoryTheory.Sites.CoverLifting

/-!
# Stacks, Chapter 1, Section 10: inherited topologies
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Pseudofunctor

universe t v' v u' u

def InheritedCoveringFamily {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C)
    {ι : Type t} {Y : ι → Pseudofunctor.CoGrothendieck F}
    {X : Pseudofunctor.CoGrothendieck F} (f : ∀ i, Y i ⟶ X) : Prop :=
  (∀ i, IsStronglyCartesian (Pseudofunctor.CoGrothendieck.forget F)
      (f i).base (f i)) ∧
    Sieve.ofArrows (fun i => (Y i).base) (fun i => (f i).base) ∈ J X.base

structure InheritedSite {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  topology : GrothendieckTopology (Pseudofunctor.CoGrothendieck F)
  coversIff : ∀ {ι : Type t} {Y : ι → Pseudofunctor.CoGrothendieck F}
    {X : Pseudofunctor.CoGrothendieck F} (f : ∀ i, Y i ⟶ X),
    Sieve.ofArrows Y f ∈ topology X ↔ InheritedCoveringFamily F J f

noncomputable def inheritedTopology {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C}
    (h : Nonempty (InheritedSite F J)) :
    GrothendieckTopology (Pseudofunctor.CoGrothendieck F) :=
  (Classical.choice h).topology

structure SiteEquivalence (A B : Type*) [Category* A] [Category* B] where
  equivalence : Nonempty (A ≌ B)
  continuous : Prop

theorem inherited_topology_exists {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) :
    Nonempty (InheritedSite F J) := by
  sorry

theorem all_morphisms_cartesian_in_groupoid_fibred_category
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    (hF : FiberwiseGroupoid F) :
    ∀ {X Y : Pseudofunctor.CoGrothendieck F} (f : X ⟶ Y),
      IsCartesian (Pseudofunctor.CoGrothendieck.forget F) f.base f := by
  sorry

theorem inherited_topology_functorial_underlying
    {C : Type u} [Category.{v} C] {F G : FiberedCategory C}
    (η : FiberedMorphism F G) :
    Pseudofunctor.CoGrothendieck.map η ⋙
        Pseudofunctor.CoGrothendieck.forget G =
      Pseudofunctor.CoGrothendieck.forget F := by
  exact Pseudofunctor.CoGrothendieck.map_comp_forget η

theorem inherited_topology_functorial
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (SF : InheritedSite F J) (SG : InheritedSite G J) :
    (Pseudofunctor.CoGrothendieck.map η).IsContinuous SF.topology SG.topology ∧
      (Pseudofunctor.CoGrothendieck.map η).IsCocontinuous SF.topology SG.topology := by
  sorry

theorem localizing_site_over_an_object
    {C : Type u} [Category.{v} C] {F : FiberedCategory C}
    {U : C} (x : Fiber F U) (hF : FiberwiseGroupoid F) :
    Nonempty (SiteEquivalence
      (CategoryTheory.Over (⟨U, x⟩ : Pseudofunctor.CoGrothendieck F))
      (CategoryTheory.Over U)) := by
  sorry

theorem stack_in_groupoids_over_stack
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : FiberedCategory C) (hF : StackInGroupoids F J)
    (S : InheritedSite F J)
    (X : FiberedCategory (Pseudofunctor.CoGrothendieck F))
    (hX : Stack X S.topology) :
    ∃ Z : FiberedCategory C, Stack Z J := by
  sorry

theorem stack_over_stack_composition
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (F : FiberedCategory C) (hF : Stack F J) (S : InheritedSite F J)
    (X : FiberedCategory (Pseudofunctor.CoGrothendieck F))
    (hX : Stack X S.topology) :
    ∃ Z : FiberedCategory C, Stack Z J := by
  sorry

end Formalization.«Books.Stacks».Unit01
