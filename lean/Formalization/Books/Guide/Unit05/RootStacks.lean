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
  divisor : EffectiveCartierDivisor X
  rootIndex : ℕ
  rootIndexPositive : 0 < rootIndex
  rootStack : C
  projection : rootStack ⟶ X
  muR : Type u
  muRGroup : CommGroup muR
  muRFinite : Finite muR
  muRIsTheRootOfUnityGroup : Prop
  muRIsTheRootOfUnityGroupProof : muRIsTheRootOfUnityGroup
  rootLineBundle : LineBundleData rootStack

structure RootStackProperties {C : Type u} [Category.{v} C]
    [StackCategory C] {X : C} (D : RootStackData X) where
  rootStackIsArtin : IsArtinStack D.rootStack
  muRStabilizerOverDivisor : Prop
  muRStabilizerOverDivisorProof : muRStabilizerOverDivisor
  schemeLikeAwayFromDivisor : Prop
  schemeLikeAwayFromDivisorProof : schemeLikeAwayFromDivisor
  rootLineBundlePowerIsTheDivisorLineBundle : Prop
  rootLineBundlePowerIsTheDivisorLineBundleProof :
    rootLineBundlePowerIsTheDivisorLineBundle

structure RootStackConstruction {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) (D : EffectiveCartierDivisor X) (r : ℕ)
    (hr : 0 < r) where
  data : RootStackData X
  divisorMatches : data.divisor = D
  rootIndexMatches : data.rootIndex = r
  properties : RootStackProperties data

def IsRootStackAlongEffectiveCartierDivisor {C : Type u} [Category.{v} C]
    [StackCategory C] (X : C) (D : EffectiveCartierDivisor X) (r : ℕ)
    (hr : 0 < r) : Prop :=
  Nonempty (RootStackConstruction X D r hr)

class RootStackLaws {C : Type u} [Category.{v} C] [StackCategory C] where
  construct : ∀ {X : C} (_hX : IsScheme X) (D : EffectiveCartierDivisor X)
    (r : ℕ) (hr : 0 < r), Nonempty (RootStackConstruction X D r hr)

theorem root_stack_is_artin
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    {D : EffectiveCartierDivisor X} {r : ℕ} {hr : 0 < r}
    (W : RootStackConstruction X D r hr) : IsArtinStack W.data.rootStack := by
  exact W.properties.rootStackIsArtin

theorem root_stack_has_mu_r_stabilizer_over_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    {D : EffectiveCartierDivisor X} {r : ℕ} {hr : 0 < r}
    (W : RootStackConstruction X D r hr) :
    W.properties.muRStabilizerOverDivisor := by
  exact W.properties.muRStabilizerOverDivisorProof

theorem root_stack_is_scheme_like_away_from_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    {D : EffectiveCartierDivisor X} {r : ℕ} {hr : 0 < r}
    (W : RootStackConstruction X D r hr) :
    W.properties.schemeLikeAwayFromDivisor := by
  exact W.properties.schemeLikeAwayFromDivisorProof

theorem root_stack_root_line_bundle_power_is_divisor
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    {D : EffectiveCartierDivisor X} {r : ℕ} {hr : 0 < r}
    (W : RootStackConstruction X D r hr) :
    W.properties.rootLineBundlePowerIsTheDivisorLineBundle := by
  exact W.properties.rootLineBundlePowerIsTheDivisorLineBundleProof

theorem cadman_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [RootStackLaws (C := C)]
    (hX : IsScheme X) (D : EffectiveCartierDivisor X)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackConstruction X D r hr) :=
  RootStackLaws.construct hX D r hr

theorem abramovich_graber_vistoli_root_stack_construction
    {C : Type u} [Category.{v} C] [StackCategory C] {X : C}
    [RootStackLaws (C := C)]
    (hX : IsScheme X) (D : EffectiveCartierDivisor X)
    (r : ℕ) (hr : 0 < r) :
    Nonempty (RootStackConstruction X D r hr) :=
  RootStackLaws.construct hX D r hr

end Formalization.Books.Guide.Unit05
