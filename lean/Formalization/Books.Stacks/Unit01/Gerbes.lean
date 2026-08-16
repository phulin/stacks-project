import Formalization.«Books.Stacks».Unit01.InheritedTopology

/-!
# Stacks, Chapter 1, Section 11: gerbes
-/

namespace Formalization.«Books.Stacks».Unit01

open CategoryTheory
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t v' v u' u

def LocallyNonempty {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  ∀ U : C, ∃ (ι : Type u) (X : ι → C) (f : ∀ i, X i ⟶ U),
    CoveringFamily J f ∧ ∀ i, Nonempty (Fiber F (X i))

def LocallyIsomorphic {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (x y : Fiber F U),
    ∃ (ι : Type u) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, Nonempty
          ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (F.map (f i).op.toLoc).toFunctor.obj y)

def IsGerbe {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧ LocallyNonempty F J ∧ LocallyIsomorphic F J

def LocallyEssentiallyInImage {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (y : Fiber G U),
    ∃ (ι : Type u) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ x : Fiber F (X i), Nonempty
          ((G.map (f i).op.toLoc).toFunctor.obj y ≅
            (η.app (.mk (op (X i)))).toFunctor.obj x)

def LocallyLiftsMorphisms {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  ∀ (U : C) (x x' : Fiber F U)
    (_b : (η.app (.mk (op U))).toFunctor.obj x ⟶
      (η.app (.mk (op U))).toFunctor.obj x'),
    ∃ (ι : Type u) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, Nonempty
          ((F.map (f i).op.toLoc).toFunctor.obj x ⟶
            (F.map (f i).op.toLoc).toFunctor.obj x')

def GerbeOver {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧ StackInGroupoids G J ∧
    LocallyEssentiallyInImage η J ∧ LocallyLiftsMorphisms η J

structure GerbeFactorizationData {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) where
  value : FiberedCategory C
  fromOriginal : FiberedMorphism F value
  toBase : FiberedMorphism value G
  isGerbe : IsGerbe value J
  equivalentToOriginal : FiberwiseEquivalence fromOriginal
  locallyEssentiallyInImage : LocallyEssentiallyInImage toBase J
  locallyLiftsMorphisms : LocallyLiftsMorphisms toBase J

def AutomorphismGroupsAbelian {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Prop :=
  ∀ (U : C) (x : Fiber F U) (a b : Aut x), a * b = b * a

structure GerbeAutomorphismSheafData {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) where
  sheaf : Sheaf J (Type u)
  abelian : Prop
  localIdentifications : Prop
  conjugationCompatible : Prop

theorem equivalent_gerbes_preserve
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (hη : FiberwiseEquivalence η) :
    IsGerbe F J ↔ IsGerbe G J := by
  sorry

theorem gerbe_characterization_by_factorization
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} (η : FiberedMorphism F G) :
    GerbeOver η J ↔ Nonempty (GerbeFactorizationData η J) := by
  sorry

theorem base_change_of_gerbe
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G : FiberedCategory C} {H K : FiberedCategory C}
    (η : FiberedMorphism F G) (θ : FiberedMorphism H K)
    (hη : GerbeOver η J) (hθ : FiberwiseEquivalence θ) :
    GerbeOver η J := by
  sorry

theorem composition_of_gerbes
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F G H : FiberedCategory C} (η : FiberedMorphism F G)
    (θ : FiberedMorphism G H) (hη : GerbeOver η J)
    (hθ : GerbeOver θ J) :
    GerbeOver (η ≫ θ) J := by
  sorry

theorem gerbe_descent
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {A B C' D : FiberedCategory C} (sq : TwoCartesianSquare A B C' D)
    (hlocal : LocallyEssentiallyInImage sq.bottom J)
    (hgerbe : GerbeOver sq.bottom J) :
    GerbeOver sq.left J := by
  sorry

theorem gerbe_abelian_automorphisms
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {F : FiberedCategory C} (hF : IsGerbe F J)
    (hAb : AutomorphismGroupsAbelian F) :
    Nonempty (GerbeAutomorphismSheafData F J) := by
  sorry

end Formalization.«Books.Stacks».Unit01
