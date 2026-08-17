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
  rootStackIsArtin : IsArtinStack rootStack
  muR : Type u
  muRGroup : Group muR
  muRIsTheRootOfUnityGroup : Prop
  muRStabilizerOverDivisor : Prop
  muRStabilizerOverDivisor_holds : muRStabilizerOverDivisor
  schemeLikeAwayFromDivisor : Prop
  schemeLikeAwayFromDivisor_holds : schemeLikeAwayFromDivisor
  rootLineBundle : LineBundleData (Point rootStack)
  rootLineBundlePowerIsTheDivisorLineBundle : Prop

def IsRootStackAlongEffectiveCartierDivisor {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) : Prop :=
  ∃ D : RootStackData X,
    IsScheme X ∧ 0 < D.rootIndex ∧ IsArtinStack D.rootStack ∧
      D.muRIsTheRootOfUnityGroup ∧ D.muRStabilizerOverDivisor ∧
      D.schemeLikeAwayFromDivisor

theorem root_stack_is_artin
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : IsArtinStack D.rootStack := by
  exact D.rootStackIsArtin

theorem root_stack_has_mu_r_stabilizer_over_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : D.muRStabilizerOverDivisor := by
  exact D.muRStabilizerOverDivisor_holds

theorem root_stack_is_scheme_like_away_from_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (D : RootStackData X) : D.schemeLikeAwayFromDivisor := by
  exact D.schemeLikeAwayFromDivisor_holds

theorem cadman_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (hX : IsScheme X) (D : EffectiveCartierDivisor (Point X))
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackData X) := by
  sorry

theorem abramovich_graber_vistoli_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    (hX : IsScheme X) (D : EffectiveCartierDivisor (Point X))
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackData X) := by
  sorry

end Formalization.Books.Guide.Unit05
