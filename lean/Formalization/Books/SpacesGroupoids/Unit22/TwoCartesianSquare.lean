import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Yoneda
import Formalization.Books.Stacks.Unit02.Foundation

/-!
# Groupoids in Algebraic Spaces, Chapter 22: the 2-cartesian square of a quotient stack

This file records the three statements in the source section.  Mathlib does
not yet have a category of algebraic spaces, so an algebraic space is exposed
here by its fppf sheaf of points together with the property selecting the
algebraic spaces.  The stack and groupoid interfaces are the categorical ones
from the preceding Stacks formalization.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v

namespace Formalization.Books.SpacesGroupoids.Unit22

/-! ## The fppf site and algebraic spaces as sheaves of points -/

abbrev FppfSite (S : Scheme.{u}) := Over S

abbrev FppfTopology (S : Scheme.{u}) : GrothendieckTopology (FppfSite S) :=
  Scheme.fppfTopology.over S

abbrev PresheafOn (C : Type u) [Category.{v} C] := Cᵒᵖ ⥤ Type v

abbrev StackOn (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v, v}

abbrev FiberOn {C : Type u} [Category.{v} C] (F : StackOn C) (T : C) :=
  Formalization.Books.Stacks.Unit01.Fiber F T

abbrev FiberedMorphismOn {C : Type u} [Category.{v} C]
    (F G : StackOn C) := F ⟶ G

abbrev MorPresheafOn {C : Type u} [Category.{v} C]
    (F : StackOn C) {T : C} (x y : FiberOn F T) :=
  Formalization.Books.Stacks.Unit01.MorPresheaf F x y

abbrev IsomPresheafOn {C : Type u} [Category.{v} C]
    (F : StackOn C) {T : C} (x y : FiberOn F T) :=
  Formalization.Books.Stacks.Unit01.IsomPresheaf F x y

/-- The fppf sheaf of points together with the predicate of being algebraic. -/
structure AlgebraicSpace (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  points : PresheafOn C
  isSheaf : Presieve.IsSheaf J points
  isAlgebraic : Prop

/-!
The pointwise pullback below is the presheaf-level fibre product used for
the relation space and for the composable-arrow space.  It is written out
so the statements do not depend on a chosen pullback object in a functor
category.
-/

def presheafPullback {C : Type u} [Category.{v} C]
    {P Q Z : PresheafOn C} (f : P ⟶ Z) (g : Q ⟶ Z) : PresheafOn C where
  obj V := { p : P.obj V × Q.obj V // f.app V p.1 = g.app V p.2 }
  map := by
    intro V W q
    exact TypeCat.ofHom (fun p : { p : P.obj V × Q.obj V //
        f.app V p.1 = g.app V p.2 } =>
      (⟨(P.map q p.1.1, Q.map q p.1.2), by
      calc
        f.app W (P.map q p.1.1) = Z.map q (f.app V p.1.1) := by
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun h => h p.1.1) (f.naturality q)
        _ = Z.map q (g.app V p.1.2) := congrArg (Z.map q) p.2
        _ = g.app W (Q.map q p.1.2) := by
          symm
          simpa only [ConcreteCategory.comp_apply] using
            congrArg (fun h => h p.1.2) (g.naturality q)⟩ :
        { p : P.obj W × Q.obj W // f.app W p.1 = g.app W p.2 }))
  map_id V := by
    ext p <;> simp
  map_comp f g := by
    ext p <;> simp

abbrev AlgebraicSpaceOver (S : Scheme.{u}) :=
  AlgebraicSpace (FppfSite S) (FppfTopology S)

abbrev SpaceHom {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (X Y : AlgebraicSpace C J) :=
  X.points ⟶ Y.points

/-! The following aliases use the shared Stacks chapter interfaces. -/

def StackInGroupoidsOn
    {C : Type u} [Category.{v} C]
    (F : StackOn C) (J : GrothendieckTopology C) : Prop :=
  Formalization.Books.Stacks.Unit01.FiberwiseGroupoid F ∧
    Formalization.Books.Stacks.Unit01.Stack F J

def StackInSetsOn
    {C : Type u} [Category.{v} C]
    (F : StackOn C) (J : GrothendieckTopology C) : Prop :=
  Formalization.Books.Stacks.Unit01.FiberwiseSet F ∧
    Formalization.Books.Stacks.Unit01.Stack F J

def CoveringFamilyOn {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {ι : Type u} {T : C}
    {T' : ι → C} (f : ∀ i, T' i ⟶ T) : Prop :=
  Formalization.Books.Stacks.Unit01.CoveringFamily J f

structure TwoFiberProductConeOn
    {C : Type u} [Category.{v} C]
    (F G H : StackOn C) where
  apex : StackOn C
  left : FiberedMorphismOn apex F
  right : FiberedMorphismOn apex G
  comparison : Prop

/-!
The following is the pointwise product of the two sheaves over the base
scheme.  On the site of schemes over `S`, the terminal sheaf is the sheaf
represented by `S`, so this is the fibre product over `S`.
-/

abbrev spaceProductOverBase
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (X Y : AlgebraicSpace C J) : PresheafOn C :=
  { obj V := X.points.obj V × Y.points.obj V
    map := by
      intro V W f
      exact TypeCat.ofHom
        (fun z : X.points.obj V × Y.points.obj V =>
          (X.points.map f z.1, Y.points.map f z.2))
    map_id V := by
      ext z <;> simp
    map_comp f g := by
      ext z <;> simp }

def spaceSectionMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {T : C} (X : AlgebraicSpace C J)
    (x : X.points.obj (op T)) : yoneda.obj T ⟶ X.points :=
  yonedaEquiv.symm x

def spaceSectionPairMap {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {T : C} (X : AlgebraicSpace C J)
    (y x : X.points.obj (op T)) :
    yoneda.obj T ⟶ spaceProductOverBase X X :=
  { app V := by
      exact TypeCat.ofHom (fun z : (yoneda.obj T).obj V =>
        ((spaceSectionMap X y).app V z, (spaceSectionMap X x).app V z))
    naturality := by
      intro V W f
      ext z
      · simpa only [CategoryTheory.types_comp_apply, TypeCat.ofHom_apply,
          TypeCat.Fun.toFun_apply] using
          congrArg (fun h => h z) ((spaceSectionMap X y).naturality f)
      · simpa only [CategoryTheory.types_comp_apply, TypeCat.ofHom_apply,
          TypeCat.Fun.toFun_apply] using
          congrArg (fun h => h z) ((spaceSectionMap X x).naturality f) }

/-! ## Groupoids, their relation map, and the associated point stacks -/

/-- The groupoid-in-algebraic-spaces data used in the quotient-stack statements. -/
structure GroupoidInAlgebraicSpaces
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (B : AlgebraicSpace C J) where
  U : AlgebraicSpace C J
  R : AlgebraicSpace C J
  source : R.points ⟶ U.points
  target : R.points ⟶ U.points
  composition : presheafPullback source target ⟶ R.points
  identity : U.points ⟶ R.points
  inverse : R.points ⟶ R.points
  structureMap : U.points ⟶ B.points
  relationStructureMap : R.points ⟶ B.points
  source_over : source ≫ structureMap = relationStructureMap
  target_over : target ≫ structureMap = relationStructureMap
  associative : Prop
  source_identity : Prop
  target_identity : Prop
  source_inverse : Prop
  target_inverse : Prop

def GroupoidInAlgebraicSpaces.arrowPair
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : AlgebraicSpace C J} (G : GroupoidInAlgebraicSpaces B) :
    G.R.points ⟶ spaceProductOverBase G.U G.U :=
  { app V := by
      exact TypeCat.ofHom (fun r : G.R.points.obj V =>
        (G.target.app V r, G.source.app V r))
    naturality := by
      intro V W f
      ext r
      · simpa only [CategoryTheory.types_comp_apply, TypeCat.ofHom_apply,
          TypeCat.Fun.toFun_apply] using
          congrArg (fun h => h r) (G.target.naturality f)
      · simpa only [CategoryTheory.types_comp_apply, TypeCat.ofHom_apply,
          TypeCat.Fun.toFun_apply] using
          congrArg (fun h => h r) (G.source.naturality f) }

/-- A stack in sets presenting the fppf sheaf of points of a space. -/
structure SpaceStack (S : Scheme.{u}) (X : AlgebraicSpaceOver S) where
  value : StackOn (FppfSite S)
  isStackInSets : StackInSetsOn value (FppfTopology S)
  pointsEquiv : ∀ T : FppfSite S,
    X.points.obj (op T) ≃ FiberOn value T

abbrev QuotientStack (S : Scheme.{u}) :=
  StackOn (FppfSite S)

/-- A fibrewise natural 2-morphism between maps of fibred categories. -/
def FiberwiseTwoMorphism
    {C : Type u} [Category.{v} C]
    {F G : StackOn C}
    (f g : FiberedMorphismOn F G) : Prop :=
  ∀ U : C, Nonempty ((f.app (.mk (op U))).toFunctor ⟶
    (g.app (.mk (op U))).toFunctor)

/-- The quotient stack, its point stacks, and the canonical arrows of the source. -/
structure QuotientStackContext (S : Scheme.{u}) where
  B : AlgebraicSpaceOver S
  groupoid : GroupoidInAlgebraicSpaces B
  quotientStack : QuotientStack S
  quotientStackIsStack : StackInGroupoidsOn quotientStack (FppfTopology S)
  UStack : SpaceStack S groupoid.U
  RStack : SpaceStack S groupoid.R
  π : FiberedMorphismOn UStack.value quotientStack
  sourceMap : FiberedMorphismOn RStack.value UStack.value
  targetMap : FiberedMorphismOn RStack.value UStack.value
  sourceMapIsInduced : Prop
  targetMapIsInduced : Prop
  canonicalTwoArrow : FiberwiseTwoMorphism (sourceMap ≫ π) (targetMap ≫ π)

/-- The image of a section of `U` in the quotient stack. -/
def quotientImage {S : Scheme.{u}}
    (D : QuotientStackContext S) {T : FppfSite S}
    (x : D.groupoid.U.points.obj (op T)) : FiberOn D.quotientStack T :=
  (D.π.app (.mk (op T))).toFunctor.obj (D.UStack.pointsEquiv T x)

/-! ## The sheaf formula for isomorphisms -/

abbrev QuotientStackIsomSheaf {S : Scheme.{u}}
    (D : QuotientStackContext S) {T : FppfSite S}
    (x y : FiberOn D.quotientStack T) :=
  IsomPresheafOn D.quotientStack x y

def restrictPresheaf {C : Type u} [Category.{v} C]
    {T : C} (P : PresheafOn C) : (Over T)ᵒᵖ ⥤ Type v :=
  (Over.forget T).op ⋙ P

def restrictPresheafMap {C : Type u} [Category.{v} C]
    {T : C} {P Q : PresheafOn C} (f : P ⟶ Q) :
    restrictPresheaf (T := T) P ⟶ restrictPresheaf (T := T) Q :=
  Functor.whiskerLeft (Over.forget T).op f

/-!
`relationPresheaf` is the literal presheaf
`T ×_{(y',x'), U ×_S U} R` on the localized site over `T`.
-/

noncomputable def relationPresheaf
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {B : AlgebraicSpace C J} (G : GroupoidInAlgebraicSpaces B)
    (T : C) (x' y' : G.U.points.obj (op T)) :
    (Over T)ᵒᵖ ⥤ Type v :=
  presheafPullback
    (restrictPresheafMap
      (T := T) (spaceSectionPairMap G.U y' x'))
    (restrictPresheafMap (T := T) (G.arrowPair))

theorem quotient_stack_morphisms {S : Scheme.{u}}
    (D : QuotientStackContext S) {T : FppfSite S}
    (x y : FiberOn D.quotientStack T)
    (x' y' : D.groupoid.U.points.obj (op T))
    (hx : x = quotientImage D x') (hy : y = quotientImage D y') :
    QuotientStackIsomSheaf D x y = relationPresheaf D.groupoid T x' y' := by
  sorry

/-! ## The 2-cartesian square -/

/-- A cone that remembers the two maps to the common quotient stack. -/
structure TwoFiberProductConeWithMaps
    {C : Type u} [Category.{v} C]
    (F G H : StackOn C)
    (f : F ⟶ H) (g : G ⟶ H)
    extends TwoFiberProductConeOn F G H where
  commutes : FiberwiseTwoMorphism (left ≫ f) (right ≫ g)

def IsTwoCartesianSquare
    {C : Type u} [Category.{v} C]
    {A B C' D : StackOn C}
    (left : A ⟶ B) (right : A ⟶ C')
    (top : B ⟶ D) (bottom : C' ⟶ D) : Prop :=
  FiberwiseTwoMorphism (left ≫ top) (right ≫ bottom) ∧
    ∃ P : TwoFiberProductConeWithMaps B C' D top bottom,
      P.apex = A ∧ HEq P.left left ∧ HEq P.right right ∧ P.comparison

theorem quotient_stack_two_cartesian {S : Scheme.{u}}
    (D : QuotientStackContext S) :
    IsTwoCartesianSquare D.sourceMap D.targetMap D.π D.π := by
  sorry

/-! ## Local algebraic-space representability of the Isom-sheaf -/

def restrictAlong {C : Type u} [Category.{v} C]
    {T' T : C} (f : T' ⟶ T) (F : (Over T)ᵒᵖ ⥤ Type v) :
    (Over T')ᵒᵖ ⥤ Type v :=
  (Over.map f).op ⋙ F

def LocallyRepresentableByAlgebraicSpace
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {T : C} (F : (Over T)ᵒᵖ ⥤ Type v) : Prop :=
  ∃ (ι : Type u) (T' : ι → C) (f : ∀ i, T' i ⟶ T),
    CoveringFamilyOn J f ∧
      ∀ i, ∃ X : AlgebraicSpace (Over (T' i)) (J.over (T' i)),
        Nonempty (restrictAlong (f i) F ≅ X.points)

theorem quotient_stack_isom {S : Scheme.{u}}
    (D : QuotientStackContext S) (T : FppfSite S)
    (x y : FiberOn D.quotientStack T) :
    LocallyRepresentableByAlgebraicSpace (FppfTopology S)
      (QuotientStackIsomSheaf D x y) := by
  sorry

end Formalization.Books.SpacesGroupoids.Unit22
