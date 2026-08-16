import Formalization.Books.Stacks.Unit01.Foundation
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Groupoids in Algebraic Spaces, Chapter 21: core interfaces

Mathlib does not yet provide the algebraic-space and quotient-stack
constructions used by this chapter.  The interfaces below keep the ambient
category of algebraic spaces abstract, while using Mathlib's categorical
pullbacks and fibred-category API for the constructions that are available.
-/

namespace Formalization.Books.SpacesGroupoids.Unit21

open CategoryTheory CategoryTheory.Limits
open Opposite
open Formalization.Books.Stacks.Unit01
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe w v u

/-! ## Internal groupoids and their morphisms -/

/-- The object-and-arrow data of a groupoid in the category of spaces over `B`.

The fields `e` and `i` expose the identity and inverse maps used explicitly in
Chapter 21.  The axioms below are supplied separately so that the pullback
formulae in the chapter can be defined independently of their proofs.
-/
structure GroupoidData (C : Type u) [Category.{v} C] [HasPullbacks C] (B : C) where
  U : C
  R : C
  U_to_B : U ⟶ B
  R_to_B : R ⟶ B
  s : R ⟶ U
  t : R ⟶ U
  s_over_B : s ≫ U_to_B = R_to_B
  t_over_B : t ≫ U_to_B = R_to_B
  c : pullback s t ⟶ R
  c_over_B : c ≫ R_to_B = pullback.fst s t ≫ R_to_B
  e : U ⟶ R
  e_over_B : e ≫ R_to_B = U_to_B
  i : R ⟶ R
  i_over_B : i ≫ R_to_B = R_to_B

/-- A pair of arrows with the composability condition for `c`.

This pointwise presentation is the categorical form of the source's
statement that the construction is a groupoid after evaluating on every test
object.
-/
def ComposablePair {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G : GroupoidData C B) (T : C) :=
  { p : (T ⟶ G.R) × (T ⟶ G.R) // p.1 ≫ G.s = p.2 ≫ G.t }

/-- The map from a composable pair into the chosen categorical pullback. -/
noncomputable def composablePairMap {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} {G : GroupoidData C B} {T : C} (p : ComposablePair G T) :
    T ⟶ pullback G.s G.t :=
  pullback.lift p.1.1 p.1.2 p.2

/-- Composition of a composable pair, evaluated on a test object. -/
noncomputable def composeAt {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G : GroupoidData C B) {T : C} (p : ComposablePair G T) :
    T ⟶ G.R :=
  composablePairMap p ≫ G.c

/-- The groupoid identities written as categorical and pointwise equations. -/
structure GroupoidAxioms {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G : GroupoidData C B) : Prop where
  comp_source : G.c ≫ G.s = pullback.snd G.s G.t ≫ G.s
  comp_target : G.c ≫ G.t = pullback.fst G.s G.t ≫ G.t
  unit_source : G.e ≫ G.s = 𝟙 G.U
  unit_target : G.e ≫ G.t = 𝟙 G.U
  inverse_source : G.i ≫ G.s = G.t
  inverse_target : G.i ≫ G.t = G.s
  left_unit : ∀ {T : C} (r : T ⟶ G.R)
      (h : (r ≫ G.t ≫ G.e) ≫ G.s = r ≫ G.t),
    composeAt G ⟨(r ≫ G.t ≫ G.e, r), h⟩ = r
  right_unit : ∀ {T : C} (r : T ⟶ G.R)
      (h : r ≫ G.s = (r ≫ G.s ≫ G.e) ≫ G.t),
    composeAt G ⟨(r, r ≫ G.s ≫ G.e), h⟩ = r
  left_inverse : ∀ {T : C} (r : T ⟶ G.R)
      (h : (r ≫ G.i) ≫ G.s = r ≫ G.t),
    composeAt G ⟨(r ≫ G.i, r), h⟩ = r ≫ G.s ≫ G.e
  right_inverse : ∀ {T : C} (r : T ⟶ G.R)
      (h : r ≫ G.s = (r ≫ G.i) ≫ G.t),
    composeAt G ⟨(r, r ≫ G.i), h⟩ = r ≫ G.t ≫ G.e
  associative : ∀ {T : C} (r₁ r₂ r₃ : T ⟶ G.R)
      (h₁₂ : r₁ ≫ G.s = r₂ ≫ G.t)
      (h₂₃ : r₂ ≫ G.s = r₃ ≫ G.t)
      (hL : composeAt G ⟨(r₁, r₂), h₁₂⟩ ≫ G.s = r₃ ≫ G.t)
      (hR : r₁ ≫ G.s = composeAt G ⟨(r₂, r₃), h₂₃⟩ ≫ G.t),
    composeAt G
        ⟨(composeAt G ⟨(r₁, r₂), h₁₂⟩, r₃), hL⟩ =
      composeAt G
        ⟨(r₁, composeAt G ⟨(r₂, r₃), h₂₃⟩), hR⟩

/-- A groupoid in algebraic spaces over `B`, expressed in an abstract ambient
category `C` with pullbacks. -/
structure GroupoidInAlgebraicSpaces (C : Type u) [Category.{v} C]
    [HasPullbacks C] (B : C) where
  data : GroupoidData C B
  axioms : GroupoidAxioms data

/-- A morphism of groupoids over the same base. -/
structure GroupoidHom {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G H : GroupoidInAlgebraicSpaces C B) where
  map_obj : G.data.U ⟶ H.data.U
  map_arr : G.data.R ⟶ H.data.R
  map_obj_over_B : map_obj ≫ H.data.U_to_B = G.data.U_to_B
  map_arr_over_B : map_arr ≫ H.data.R_to_B = G.data.R_to_B
  map_source : map_arr ≫ H.data.s = G.data.s ≫ map_obj
  map_target : map_arr ≫ H.data.t = G.data.t ≫ map_obj
  map_identity : G.data.e ≫ map_arr = map_obj ≫ H.data.e
  map_inverse : G.data.i ≫ map_arr = map_arr ≫ H.data.i
  map_composition : ∀ {T : C} (p : ComposablePair G.data T)
      (q : ComposablePair H.data T),
    q.1.1 = p.1.1 ≫ map_arr →
    q.1.2 = p.1.2 ≫ map_arr →
    composeAt H.data q = composeAt G.data p ≫ map_arr

/-! ## Quotient-stack interfaces -/

/-- A fixed-universe version of the fibred-category presentation used for
the stack interfaces in this chapter.  Fixing the target universe makes the
hom-types of quotient-stack values definitionally compatible. -/
abbrev StackFiberedCategory (D : Type u) [Category.{v} D] :=
  FiberedCategory.{v, v, u} D

/-- View a space over `B` as a space over `S`. -/
def overS {C : Type u} [Category.{v} C] {S B : C} (B_to_S : B ⟶ S)
    (X : C) (X_to_B : X ⟶ B) : Over S :=
  Over.mk (X_to_B ≫ B_to_S)

/-- The representable fibred category attached to an object over `S`.

This is the discrete-category Yoneda construction.  It uses the established
`LocallyDiscrete.mkPseudofunctor` constructor, so the opposite in the
fibred-category base is handled at the type level.
-/
noncomputable def RepresentableStack {C : Type u} [Category.{v} C]
    {S : C} (X : Over S) :
    StackFiberedCategory (Over S) :=
  LocallyDiscrete.mkPseudofunctor
    (fun T : (Over S)ᵒᵖ => Cat.of (Discrete (T.unop ⟶ X)))
    (fun {T₁ T₂} f =>
      (Discrete.functor (fun g : T₁.unop ⟶ X => Discrete.mk (f.unop ≫ g))).toCatHom)
    (fun _ => by sorry)
    (fun _ _ => by sorry)

/-- A groupoid structure map from `G` to a space `X` over the same base. -/
structure GroupoidBaseMap {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G : GroupoidInAlgebraicSpaces C B) (X : C) (X_to_B : X ⟶ B) where
  object : G.data.U ⟶ X
  arrow : G.data.R ⟶ X
  source : G.data.s ≫ object = arrow
  target : G.data.t ≫ object = arrow
  object_over_B : object ≫ X_to_B = G.data.U_to_B
  arrow_over_B : arrow ≫ X_to_B = G.data.R_to_B

/-- The identity structure map of a groupoid to its base. -/
def groupoidBaseMap {C : Type u} [Category.{v} C] [HasPullbacks C]
    {B : C} (G : GroupoidInAlgebraicSpaces C B) :
    GroupoidBaseMap G B (𝟙 B) where
  object := G.data.U_to_B
  arrow := G.data.R_to_B
  source := G.data.s_over_B
  target := G.data.t_over_B
  object_over_B := by simp
  arrow_over_B := by simp

/-- A quotient stack model over the chosen fppf-like topology `J`.

The value and its stack property are the part supplied by the earlier
stackification construction.  The `fromObject` and `mapTo` fields expose the
canonical arrows from the source and to any base over which the groupoid is
defined; this is exactly the API used by the present chapter.
-/
structure QuotientStack {C : Type u} [Category.{v} C] [HasPullbacks C]
    (S : C) (J : GrothendieckTopology (Over S))
    {B : C} (B_to_S : B ⟶ S)
    (G : GroupoidInAlgebraicSpaces C B) where
  value : StackFiberedCategory (Over S)
  isStack : Stack value J
  fromObject :
    RepresentableStack (overS B_to_S G.data.U G.data.U_to_B) ⟶ value
  mapTo : ∀ {X : C} (X_to_B : X ⟶ B),
    GroupoidBaseMap G X X_to_B →
      (value ⟶ RepresentableStack (overS B_to_S X X_to_B))

/-- A 1-morphism between two chosen quotient-stack models. -/
abbrev QuotientStackMorphism {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S : C} {J : GrothendieckTopology (Over S)}
    {B : C} {B_to_S : B ⟶ S}
    {G H : GroupoidInAlgebraicSpaces C B}
    (X : QuotientStack S J B_to_S G)
    (Y : QuotientStack S J B_to_S H) :=
  X.value ⟶ Y.value

/-- The canonical map from a quotient stack to the stack of its base. -/
def QuotientStack.toBase {C : Type u} [Category.{v} C] [HasPullbacks C]
    {S : C} {J : GrothendieckTopology (Over S)}
    {B : C} {B_to_S : B ⟶ S}
    {G : GroupoidInAlgebraicSpaces C B}
    (X : QuotientStack S J B_to_S G) :
    X.value ⟶ RepresentableStack (overS B_to_S B (𝟙 B)) :=
  X.mapTo (𝟙 B) (groupoidBaseMap G)

/-- A 2-morphism interface for fibred-category morphisms.  The established
`Pseudofunctor.StrongTrans` bicategory supplies its morphisms as modifications. -/
def FiberedTwoMorphism {D : Type u} [Category.{v} D]
    {F G : StackFiberedCategory D} (α β : F ⟶ G) : Prop :=
  Nonempty (α ⟶ β)

/-- A square of stacks whose commutativity is allowed to be a 2-morphism. -/
structure QuotientStackCartesianSquare {D : Type u} [Category.{v} D]
    (A B C' E : StackFiberedCategory D) where
  left : A ⟶ B
  right : A ⟶ C'
  top : B ⟶ E
  bottom : C' ⟶ E
  commutes : FiberedTwoMorphism (left ≫ top) (right ≫ bottom)
  isTwoPullback : Prop

end Formalization.Books.SpacesGroupoids.Unit21
