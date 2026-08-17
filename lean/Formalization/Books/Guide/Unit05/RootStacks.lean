import Formalization.Books.Guide.Unit05.Core

/-!
# Chapter 5, Section 13: taking roots of line bundles
-/

noncomputable section

open CategoryTheory

universe u v

namespace Formalization.Books.Guide.Unit05

structure RootStackData {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  baseIsScheme : IsScheme X
  divisor : EffectiveCartierDivisor (Point X)
  rootIndex : ℕ
  rootIndexPositive : 0 < rootIndex
  rootStack : C
  projection : rootStack ⟶ X
  muR : Type u
  muRGroup : Group muR
  muRIsTheRootOfUnityGroup : Prop
  rootLineBundle : LineBundleData (Point rootStack)

structure RootStackProperties {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : RootStackData X) where
  rootStackIsArtin : IsArtinStack D.rootStack
  muRStabilizerOverDivisor : Prop
  schemeLikeAwayFromDivisor : Prop
  rootLineBundlePowerIsTheDivisorLineBundle : Prop

structure RootStackConstruction {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) where
  data : RootStackData X
  properties : RootStackProperties data

def IsRootStackAlongEffectiveCartierDivisor {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  Nonempty (RootStackConstruction X)

theorem root_stack_is_artin
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : Nonempty (RootStackProperties D) := by
  sorry

theorem root_stack_has_mu_r_stabilizer_over_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : Nonempty (RootStackProperties D) := by
  sorry

theorem root_stack_is_scheme_like_away_from_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : Nonempty (RootStackProperties D) := by
  sorry

theorem cadman_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (hX : IsScheme X) (D : EffectiveCartierDivisor (Point X))
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackConstruction X) := by
  sorry

theorem abramovich_graber_vistoli_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (hX : IsScheme X) (D : EffectiveCartierDivisor (Point X))
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackConstruction X) := by
  sorry

end Formalization.Books.Guide.Unit05
