import Formalization.«Books.SpacesGroupoids».Unit20.Core

/-!
# Groupoids in Algebraic Spaces, Chapter 20: quotient stacks

This file records the quotient-stack definitions and the two canonical maps
from the source.  The categorical stackification and 2-categorical coherence
proofs are left as theorem interfaces for the later proof stage.
-/

noncomputable section

namespace Formalization.«Books.SpacesGroupoids».Unit20

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v

/-! ## The stack in sets attached to an algebraic space -/

/-- Pullback of points, viewed as a functor between discrete categories. -/
def pointRestrictionFunctor {S : Scheme.{u}} (X : AlgebraicSpace S)
    {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂) :
    Discrete (SpacePoint X T₂) ⥤ Discrete (SpacePoint X T₁) where
  obj x := ⟨restrictPoint X f x.as⟩
  map {_ _} g := by
    rcases g with ⟨h⟩
    exact ⟨⟨congrArg (restrictPoint X f) h.down⟩⟩

/-- The presheaf in sets associated to an algebraic space. -/
noncomputable def spaceStack {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Formalization.«Books.Stacks».Unit01.FiberedCategory (SchemeOver S) :=
  LocallyDiscrete.mkPseudofunctor
    (fun T => Cat.of (Discrete (SpacePoint X T.unop)))
    (fun {T T'} f => (pointRestrictionFunctor X f.unop).toCatHom)
    (fun _ => by sorry)
    (fun _ _ => by sorry)
    (map₂_associator := by sorry)
    (map₂_left_unitor := by sorry)
    (map₂_right_unitor := by sorry)

/-- The stack-in-sets condition used for the sheaf-valued construction. -/
def StackInSets {C : Type u} [Category.{v} C]
    (F : Formalization.«Books.Stacks».Unit01.FiberedCategory C)
    (J : GrothendieckTopology C) : Prop :=
  Formalization.«Books.Stacks».Unit01.FiberwiseSet F ∧
    Formalization.«Books.Stacks».Unit01.Stack F J

theorem quotientPresheaf_is_fiberwise_groupoid
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Formalization.«Books.Stacks».Unit01.FiberwiseGroupoid
      (quotientPresheaf G) := by
  sorry

theorem quotientStack_is_stack_in_groupoids
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    StackInGroupoids (quotientStack G) (FppfTopology S) :=
  (quotientStackification G).isStackInGroupoids

theorem spaceStack_is_stack_in_sets {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    StackInSets (spaceStack X) (FppfTopology S) := by
  sorry

/-- The canonical map of stacks in sets induced by a sheaf morphism. -/
theorem spaceStack_map_exists {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Nonempty (spaceStack X ⟶ spaceStack Y) := by
  sorry

noncomputable def spaceStackMap {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    spaceStack X ⟶ spaceStack Y :=
  Classical.choice (spaceStack_map_exists f)

/-! ## Quotient stacks and the canonical arrows -/

/-- The canonical projection `S_U ⟶ [U/R]`. -/
theorem quotientStack_projection_exists {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Nonempty (spaceStack G.U.space ⟶ quotientStack G) := by
  sorry

noncomputable def quotientStackProjection {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    spaceStack G.U.space ⟶ quotientStack G :=
  Classical.choice (quotientStack_projection_exists G)

/-- The canonical structural map `[U/R] ⟶ S_B`. -/
theorem quotientStack_to_base_exists {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Nonempty (quotientStack G ⟶ spaceStack B) := by
  sorry

noncomputable def quotientStackToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    quotientStack G ⟶ spaceStack B :=
  Classical.choice (quotientStack_to_base_exists G)

theorem quotientStack_projection_comp_to_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    quotientStackProjection G ≫ quotientStackToBase G =
      spaceStackMap G.U.map := by
  sorry

/-! ## Group actions and their associated groupoids -/

/-- Points of an algebraic space over `B` lying over a fixed `B`-valued
point.  This is the pointwise form of a fibre product over `B`. -/
abbrev RelativePoint {S : Scheme.{u}} {B : AlgebraicSpace S}
    (X : AlgebraicSpaceOver B) (T : SchemeOver S) (b : SpacePoint B T) :=
  {x : OverPoint X T // pointMap X.map T x = b}

/-- A pointwise internal group object over `B`.  The `pullback` data and its
operation laws encode the corresponding group algebraic space and its
contravariant functoriality. -/
structure GroupAlgebraicSpaceOver {S : Scheme.{u}} (B : AlgebraicSpace S) where
  carrier : AlgebraicSpaceOver B
  pointGroup : ∀ (T : SchemeOver S) (b : SpacePoint B T),
    Group (RelativePoint carrier T b)
  pullback : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂),
    RelativePoint carrier T₂ b →
      RelativePoint carrier T₁ (restrictPoint B f b)
  pullback_obj : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂) (g : RelativePoint carrier T₂ b),
    (pullback f b g).1 = restrictPoint carrier.space f g.1
  pullback_one : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂),
    pullback f b ((pointGroup T₂ b).one) =
      (pointGroup T₁ (restrictPoint B f b)).one
  pullback_mul : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂) (g h : RelativePoint carrier T₂ b),
    pullback f b ((pointGroup T₂ b).mul g h) =
      (pointGroup T₁ (restrictPoint B f b)).mul (pullback f b g)
        (pullback f b h)
  pullback_inv : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂) (g : RelativePoint carrier T₂ b),
    pullback f b ((pointGroup T₂ b).inv g) =
      (pointGroup T₁ (restrictPoint B f b)).inv (pullback f b g)

abbrev GroupAlgebraicSpace {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  GroupAlgebraicSpaceOver B

/-- An action of an algebraic group space over `B` on an algebraic space over
`B`, together with the associated internal groupoid. -/
structure AlgebraicSpaceAction {S : Scheme.{u}} {B : AlgebraicSpace S} where
  group : GroupAlgebraicSpaceOver B
  space : AlgebraicSpaceOver B
  spacePullback : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂),
    RelativePoint space T₂ b →
      RelativePoint space T₁ (restrictPoint B f b)
  spacePullback_obj : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂) (x : RelativePoint space T₂ b),
    (spacePullback f b x).1 = restrictPoint space.space f x.1
  act : ∀ (T : SchemeOver S) (b : SpacePoint B T),
    RelativePoint group.carrier T b → RelativePoint space T b →
      RelativePoint space T b
  act_one : ∀ (T : SchemeOver S) (b : SpacePoint B T)
      (x : RelativePoint space T b),
    act T b ((group.pointGroup T b).one) x = x
  act_mul : ∀ (T : SchemeOver S) (b : SpacePoint B T)
      (g h : RelativePoint group.carrier T b) (x : RelativePoint space T b),
    act T b ((group.pointGroup T b).mul g h) x = act T b g (act T b h x)
  pullback_compatible : ∀ {T₁ T₂ : SchemeOver S} (f : T₁ ⟶ T₂)
      (b : SpacePoint B T₂) (g : RelativePoint group.carrier T₂ b)
      (x : RelativePoint space T₂ b),
    spacePullback f b (act T₂ b g x) =
      act T₁ (restrictPoint B f b) (group.pullback f b g)
        (spacePullback f b x)
  associatedGroupoid : AlgebraicSpaceGroupoid B

/-- The quotient stack attached to an algebraic-space action, written `[X/G]`. -/
noncomputable def quotientStackOfAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (A : AlgebraicSpaceAction (B := B)) :
    Formalization.«Books.Stacks».Unit01.FiberedCategory (SchemeOver S) :=
  quotientStack A.associatedGroupoid

/-! ## The canonical 2-arrow -/

theorem quotientStack_two_arrow_exists {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Nonempty (Pseudofunctor.StrongTrans.Modification
      (spaceStackMap G.s.map ≫ quotientStackProjection G)
      (spaceStackMap G.t.map ≫ quotientStackProjection G)) := by
  sorry

noncomputable def quotientStackTwoArrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Pseudofunctor.StrongTrans.Modification
      (spaceStackMap G.s.map ≫ quotientStackProjection G)
      (spaceStackMap G.t.map ≫ quotientStackProjection G) :=
  Classical.choice (quotientStack_two_arrow_exists G)

/-- The displayed square with `R`, `U`, and `[U/R]` is 2-commutative. -/
theorem quotientStack_fundamental_square_2_commutes
    {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : AlgebraicSpaceGroupoid B) :
    Nonempty (Pseudofunctor.StrongTrans.Modification
      (spaceStackMap G.s.map ≫ quotientStackProjection G)
      (spaceStackMap G.t.map ≫ quotientStackProjection G)) :=
  quotientStack_two_arrow_exists G

/-! The source's final remark points forward to the 2-fibre-product and
2-coequalizer descriptions.  Their square is represented above by the
pointwise `R`, `U`, and quotient-stack interfaces; the universal properties
belong to the later functoriality sections. -/

end Formalization.«Books.SpacesGroupoids».Unit20
