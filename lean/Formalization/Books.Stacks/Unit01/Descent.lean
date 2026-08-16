import Formalization.«Books.Stacks».Unit01.Foundation

/-!
# Stacks, Chapter 1, Section 3: descent data

The generalized `Pseudofunctor.DescentData` API is used here.  It does not
require chosen binary or triple pullbacks, and its compatibility fields imply
the isomorphism and cocycle identities used in the book.
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open CategoryTheory.Pseudofunctor
open Opposite

universe t t' v' v u' u

structure DescentCover (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  index : Type t
  base : C
  object : index → C
  arrow : ∀ i, object i ⟶ base
  covering : CoveringFamily J arrow

abbrev DescentCategory {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) := F.DescentData f

abbrev DescentMorphism {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} (D E : F.DescentData f) := D ⟶ E

def canonicalDescentData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) (M : Fiber F U) : F.DescentData f :=
  Pseudofunctor.DescentData.ofObj (F := F) M

def pullbackDescentData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {ι ι' : Type*} {U U' : C}
    {X : ι → C} {X' : ι' → C} {f : ∀ i, X i ⟶ U}
    {f' : ∀ j, X' j ⟶ U'} (p : U' ⟶ U) (α : ι' → ι)
    (p' : ∀ j, X' j ⟶ X (α j))
    (w : ∀ j, p' j ≫ f (α j) = f' j ≫ p) :
    F.DescentData f ⥤ F.DescentData f' :=
  Pseudofunctor.DescentData.pullFunctor (F := F) w

theorem descent_data_diagonal {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} (D : F.DescentData f) {Y : C} (q : Y ⟶ U)
    {i : ι} (g : Y ⟶ X i) (hg : g ≫ f i = q) :
    D.hom q g g hg hg = 𝟙 _ :=
  D.hom_self q g hg

theorem descent_data_inverse {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {ι : Type t} {U : C} {X : ι → C}
    {f : ∀ i, X i ⟶ U} (D : F.DescentData f) {Y : C} (q : Y ⟶ U)
    {i₁ i₂ : ι} (g₁ : Y ⟶ X i₁) (g₂ : Y ⟶ X i₂)
    (hg₁ : g₁ ≫ f i₁ = q) (hg₂ : g₂ ≫ f i₂ = q) :
    D.hom q g₁ g₂ hg₁ hg₂ ≫ D.hom q g₂ g₁ hg₂ hg₁ = 𝟙 _ := by
  sorry

theorem canonical_descent_data_components {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) (M : Fiber F U) (i : ι) :
    (canonicalDescentData F f M).obj i =
      (F.map (f i).op.toLoc).toFunctor.obj M := by
  rfl

theorem canonical_descent_data_is_effective {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) (M : Fiber F U) :
    EffectiveDescentData F f (canonicalDescentData F f M) := by
  refine ⟨M, ?_⟩
  change Nonempty ((F.toDescentData f).obj M ≅ (F.toDescentData f).obj M)
  exact ⟨Iso.refl _⟩

theorem pullback_descent_data_independent {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {ι ι' : Type*} {U U' : C}
    {X : ι → C} {X' : ι' → C} {f : ∀ i, X i ⟶ U}
    {f' : ∀ j, X' j ⟶ U'} {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)}
    {p : U' ⟶ U} (w w' : ∀ j, p' j ≫ f (α j) = f' j ≫ p) :
    Nonempty
      (Pseudofunctor.DescentData.pullFunctor (F := F) w ≅
        Pseudofunctor.DescentData.pullFunctor (F := F) w') := by
  sorry

theorem descent_comparison_of_stack {C : Type u} [Category.{v} C]
    {F : FiberedCategory C} {J : GrothendieckTopology C}
    [F.IsStack J] {ι : Type t} {U : C} {X : ι → C}
    (f : ∀ i, X i ⟶ U) (hf : CoveringFamily J f) :
    (F.toDescentData f).IsEquivalence :=
  F.isEquivalence_toDescentData f hf

end Formalization.«Books.Stacks».Unit01
