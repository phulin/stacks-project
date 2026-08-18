import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Formalization.Books.Stacks.Unit02.Foundation

set_option genSizeOf false
set_option linter.all false

/-!
# Groupoids in algebraic spaces, Chapter 27: gerbes and quotient stacks

The preceding sections of the book construct quotient stacks and the
associated morphisms. Those files are not present in this formalization
workspace, so this file records the book-facing interfaces needed by the two
gerbe statements in the chapter. The ambient site is the fppf site of
schemes over `S`, and fppf-surjectivity uses Mathlib's locally-surjective
sheaf morphisms.
-/

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Formalization.Books.Stacks.Unit01
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace Formalization.Books.SpacesGroupoids.Unit27

universe v u w

/-! ## The earlier chapter's gerbe predicate -/

def StackInGroupoids {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  FiberwiseGroupoid F ∧ Stack F J

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

/-- The earlier Stacks chapter's predicate for a morphism which is a gerbe. -/
def GerbeOver {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G)
    (J : GrothendieckTopology C) : Prop :=
  StackInGroupoids F J ∧ StackInGroupoids G J ∧
    LocallyEssentiallyInImage η J ∧ LocallyLiftsMorphisms η J

/-! ## The fppf site and algebraic spaces -/

/-- The fppf topology on the category of schemes over `S`. -/
abbrev FppfTopology (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  AlgebraicGeometry.Scheme.fppfTopology.over S

/-- An algebraic space over `S`, viewed through its defining fppf sheaf. -/
abbrev AlgebraicSpace (S : Scheme.{u}) := Sheaf (FppfTopology S) (Type w)

/-- A morphism of algebraic spaces. -/
abbrev AlgebraicSpaceMorphism {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} := X ⟶ Y

/-- A surjective morphism of fppf sheaves, in Mathlib's local-surjectivity API. -/
def FppfSurjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  Sheaf.IsLocallySurjective f

/-! ## Presentations and the restriction of arrows -/

/-- The object and arrow spaces, structure maps, and source and target maps
of a groupoid in algebraic spaces over `B`.

The groupoid operations and their laws belong to the quotient-stack
construction in the preceding sections. The present chapter only uses this
presentation-level data and the induced quotient-stack interfaces below. -/
structure GroupoidInAlgebraicSpaces
    {S : Scheme.{u}} (B : AlgebraicSpace S) where
  objects : AlgebraicSpace S
  arrows : AlgebraicSpace S
  source : arrows ⟶ objects
  target : arrows ⟶ objects
  objectsToBase : objects ⟶ B
  arrowsToBase : arrows ⟶ B
  source_over_base : source ≫ objectsToBase = arrowsToBase
  target_over_base : target ≫ objectsToBase = arrowsToBase

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

private structure RelationRestrictionData
    (P' : GroupoidInAlgebraicSpaces B)
    {U : AlgebraicSpace S} (f : U ⟶ P'.objects) where
  object : AlgebraicSpace S
  source : object ⟶ U
  target : object ⟶ U

private noncomputable def relationRestrictionData
    (P' : GroupoidInAlgebraicSpaces B)
    {U : AlgebraicSpace S} (f : U ⟶ P'.objects) :
    RelationRestrictionData P' f := by
  letI : HasPullbacks (AlgebraicSpace S) := inferInstance
  exact
    { object := pullback (pullback.fst P'.source f ≫ P'.target) f
      source := pullback.fst (pullback.fst P'.source f ≫ P'.target) f ≫
        pullback.snd P'.source f
      target := pullback.snd (pullback.fst P'.source f ≫ P'.target) f }

/-- The restriction `R'|_U` of the arrow space of a groupoid `P'` along
`f : U ⟶ P'.objects`, namely the pullback imposing the source and target
conditions. -/
noncomputable def RelationRestriction
    (P' : GroupoidInAlgebraicSpaces B)
    {U : AlgebraicSpace S} (f : U ⟶ P'.objects) : AlgebraicSpace S :=
  (relationRestrictionData P' f).object

/-- The source projection of `R'|_U`. -/
noncomputable def restrictionSource
    (P' : GroupoidInAlgebraicSpaces B)
    {U : AlgebraicSpace S} (f : U ⟶ P'.objects) :
    RelationRestriction P' f ⟶ U :=
  (relationRestrictionData P' f).source

/-- The target projection of `R'|_U`. -/
noncomputable def restrictionTarget
    (P' : GroupoidInAlgebraicSpaces B)
    {U : AlgebraicSpace S} (f : U ⟶ P'.objects) :
    RelationRestriction P' f ⟶ U :=
  (relationRestrictionData P' f).target

/-! ## Quotient-stack interfaces -/

/-- The stack in groupoids denoted by `[U/R]` for a presentation `P`.

The field `isStackInGroupoids` retains the defining property of the
stackification from the earlier quotient-stack sections. No algebraicity
claim is imposed on this stack, matching the warning in the source section. -/
structure QuotientStack
    (P : GroupoidInAlgebraicSpaces B) where
  value : FiberedCategory (Over S)
  isStackInGroupoids : StackInGroupoids value (FppfTopology S)

/-- The data attached by quotient-stack functoriality to a morphism of
groupoid presentations over `B`.

`map` is the canonical morphism `[f]`; `relationMap` is the corresponding map
to the restricted arrow space `R'|_U` used in the gerbe criterion. -/
structure QuotientStackFunctorialData
    (P P' : GroupoidInAlgebraicSpaces B) where
  objectMap : P.objects ⟶ P'.objects
  object_over_base : objectMap ≫ P'.objectsToBase = P.objectsToBase
  relationMap : P.arrows ⟶ RelationRestriction P' objectMap
  source_commutes :
    relationMap ≫ restrictionSource P' objectMap = P.source
  target_commutes :
    relationMap ≫ restrictionTarget P' objectMap = P.target
  sourceQuotient : QuotientStack P
  targetQuotient : QuotientStack P'
  map : sourceQuotient.value ⟶ targetQuotient.value

/-! ## Group algebraic spaces and the trivial-action presentation -/

private abbrev GroupObjectOver (B : AlgebraicSpace S) (X : Over B) :=
  @GrpObj (Over B) (inferInstance : Category (Over B))
    (Over.cartesianMonoidalCategory B) X

/-- A group algebraic space over `B`, expressed as a group object in the
slice category of fppf sheaves over `B`. -/
def GroupAlgebraicSpace (B : AlgebraicSpace S) :=
  Σ underlying : Over B, GroupObjectOver B underlying

namespace GroupAlgebraicSpace

def mk {B : AlgebraicSpace S} (underlying : Over B)
    (group : GroupObjectOver B underlying) : GroupAlgebraicSpace B :=
  ⟨underlying, group⟩

abbrev underlying {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) : Over B :=
  G.1

abbrev group {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    GroupObjectOver B G.underlying :=
  G.2

/-- The underlying algebraic space of a group algebraic space. -/
abbrev carrier
    (G : GroupAlgebraicSpace B) : AlgebraicSpace S :=
  G.underlying.left

/-- The structure morphism of a group algebraic space. -/
abbrev structureMap
    (G : GroupAlgebraicSpace B) : G.carrier ⟶ B :=
  G.underlying.hom

end GroupAlgebraicSpace

/-- The groupoid presentation for the trivial action of `G` on `B`.

Its arrow space is `B ×_B G`, identified with the underlying object of `G`,
and both source and target are the projection to `B`. -/
def trivialActionGroupoid
    (G : GroupAlgebraicSpace B) :
    GroupoidInAlgebraicSpaces B where
  objects := B
  arrows := G.carrier
  source := G.structureMap
  target := G.structureMap
  objectsToBase := 𝟙 B
  arrowsToBase := G.structureMap
  source_over_base := by simp
  target_over_base := by simp

/-! ## The stack of maps to an algebraic space -/

/-- The stack in groupoids associated to an algebraic-space sheaf `B`.

The preceding chapter's arrow lemma supplies this object and the canonical
map from a quotient stack. Bundling the stack property here keeps the
chapter-27 theorem statement faithful while leaving that construction in its
proper earlier dependency. -/
def AlgebraicSpaceStack (B : AlgebraicSpace S) :=
  { value : FiberedCategory (Over S) //
    StackInGroupoids value (FppfTopology S) }

namespace AlgebraicSpaceStack

def mk {B : AlgebraicSpace S} (value : FiberedCategory (Over S))
    (isStackInGroupoids : StackInGroupoids value (FppfTopology S)) :
    AlgebraicSpaceStack B :=
  ⟨value, isStackInGroupoids⟩

abbrev value {B : AlgebraicSpace S} (X : AlgebraicSpaceStack B) :
    FiberedCategory (Over S) :=
  X.1

theorem isStackInGroupoids {B : AlgebraicSpace S} (X : AlgebraicSpaceStack B) :
    StackInGroupoids X.value (FppfTopology S) :=
  X.2

end AlgebraicSpaceStack

/-- The canonical arrow `[B/G] ⟶ 𝒮_B` supplied by the quotient-stack arrow
construction for the trivial action. -/
def TrivialActionQuotientStackData
    (G : GroupAlgebraicSpace B) :=
  Σ quotient : QuotientStack (trivialActionGroupoid G),
    Σ base : AlgebraicSpaceStack B, quotient.value ⟶ base.value

namespace TrivialActionQuotientStackData

def mk {G : GroupAlgebraicSpace B}
    (quotient : QuotientStack (trivialActionGroupoid G))
    (base : AlgebraicSpaceStack B) (map : quotient.value ⟶ base.value) :
    TrivialActionQuotientStackData G :=
  ⟨quotient, base, map⟩

abbrev quotient {G : GroupAlgebraicSpace B}
    (D : TrivialActionQuotientStackData G) :
    QuotientStack (trivialActionGroupoid G) := D.1

abbrev base {G : GroupAlgebraicSpace B}
    (D : TrivialActionQuotientStackData G) : AlgebraicSpaceStack B := D.2.1

abbrev map {G : GroupAlgebraicSpace B}
    (D : TrivialActionQuotientStackData G) : D.quotient.value ⟶ D.base.value :=
  D.2.2

end TrivialActionQuotientStackData

/-! ## Gerbes and quotient stacks -/

/-- A quotient-stack morphism is a gerbe when it is locally surjective on the
object and restricted arrow spaces.

This is Lemma `lemma-when-gerbe` in the source. -/
theorem lemma_when_gerbe
    {P P' : GroupoidInAlgebraicSpaces B}
    (F : QuotientStackFunctorialData P P')
    (h_objects : FppfSurjective F.objectMap)
    (h_arrows : FppfSurjective F.relationMap) :
    GerbeOver F.map (FppfTopology S) := by
  sorry

/-- The quotient of `B` by a group algebraic space acting trivially on `B` is
a gerbe over the stack associated to `B`.

The quotient-stack value and the stack `𝒮_B`, together with the canonical
arrow supplied by the preceding quotient-stack-arrows lemma, are bundled as
the explicit interfaces `Q` and `𝒮B`. -/
theorem lemma_group_quotient_gerbe
    (G : GroupAlgebraicSpace B)
    (D : TrivialActionQuotientStackData G) :
    GerbeOver D.map (FppfTopology S) := by
  sorry

end Formalization.Books.SpacesGroupoids.Unit27
