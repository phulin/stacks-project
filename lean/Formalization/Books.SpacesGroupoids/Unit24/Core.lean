import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Algebraic Spaces and Groupoids, Chapter 24: core interfaces

This file records the concrete categorical data used in the explicit
description of a quotient stack.  The ambient category is kept abstract: it
may be instantiated by a category of algebraic spaces, while `J` is its fppf
topology.  The chosen pullbacks make the pair and triple fibre products in the
text available as actual categorical objects.
-/

namespace Formalization.«Books.SpacesGroupoids».Unit24

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe t u v w

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The pseudofunctor presentation of a category fibred in groupoids over
the ambient site. -/
abbrev FiberedCategory (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}

/-- The fibre of a fibred category over an object of the site. -/
abbrev Fiber (F : FiberedCategory C) (T : C) :=
  F.obj (.mk (op T))

/-- A scheme over `S`, represented by an object of the ambient category over `S`. -/
abbrev SchemeOver (S : C) := Over S

/-- An fppf covering of a fixed object `T` over `S`.

The field `covering` uses the established `CoveringFamily`/sieve interface;
the extra `overS` field records that every member of the family is a scheme
over the same base. -/
structure FppfCover (J : GrothendieckTopology C) {S : C} (T : SchemeOver S) where
  index : Type t
  object : index → C
  arrow : ∀ i, object i ⟶ T.left
  objectToS : ∀ i, object i ⟶ S
  overS : ∀ i, arrow i ≫ T.hom = objectToS i
  covering : Sieve.ofArrows object arrow ∈ J T.left

namespace FppfCover

variable {J : GrothendieckTopology C} {S : C} {T : SchemeOver S}
  (𝒯 : FppfCover J T)

/-- The chosen overlap `Tᵢ ×_T Tⱼ`. -/
abbrev pair (i j : 𝒯.index) : C := pullback (𝒯.arrow i) (𝒯.arrow j)

/-- The two projections from an overlap. -/
abbrev pairPr0 (i j : 𝒯.index) : pair 𝒯 i j ⟶ 𝒯.object i :=
  pullback.fst (𝒯.arrow i) (𝒯.arrow j)

abbrev pairPr1 (i j : 𝒯.index) : pair 𝒯 i j ⟶ 𝒯.object j :=
  pullback.snd (𝒯.arrow i) (𝒯.arrow j)

/-- The map from an overlap to the common base. -/
abbrev pairToBase (i j : 𝒯.index) : pair 𝒯 i j ⟶ T.left :=
  pairPr0 𝒯 i j ≫ 𝒯.arrow i

/-- The map from an overlap to `S`, using either member of the cover. -/
abbrev pairToS (i j : 𝒯.index) : pair 𝒯 i j ⟶ S :=
  pairPr0 𝒯 i j ≫ 𝒯.objectToS i

theorem pairToS_eq (i j : 𝒯.index) :
    pairToS 𝒯 i j = pairPr1 𝒯 i j ≫ 𝒯.objectToS j := by
  calc
    pairToS 𝒯 i j =
        pairPr0 𝒯 i j ≫ (𝒯.arrow i ≫ T.hom) := by
          rw [𝒯.overS i]
    _ = (pairPr0 𝒯 i j ≫ 𝒯.arrow i) ≫ T.hom := by
      simp only [Category.assoc]
    _ = (pairPr1 𝒯 i j ≫ 𝒯.arrow j) ≫ T.hom := by
      rw [pullback.condition]
    _ = pairPr1 𝒯 i j ≫ 𝒯.objectToS j := by
      rw [← 𝒯.overS j, Category.assoc]

/-- The chosen triple overlap, formed by first taking `Tᵢ ×_T Tⱼ`. -/
def triple (i j k : 𝒯.index) : C :=
  pullback (pairToBase 𝒯 i j) (𝒯.arrow k)

abbrev tripleFirst (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ pair 𝒯 i j :=
  pullback.fst (pairToBase 𝒯 i j) (𝒯.arrow k)

abbrev tripleLast (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ 𝒯.object k :=
  pullback.snd (pairToBase 𝒯 i j) (𝒯.arrow k)

abbrev tripleMiddle (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ 𝒯.object j :=
  tripleFirst 𝒯 i j k ≫ pairPr1 𝒯 i j

/-- The projection `Tᵢ ×_T Tⱼ ×_T Tₖ → Tᵢ ×_T Tⱼ`. -/
abbrev triplePr01 (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ pair 𝒯 i j :=
  tripleFirst 𝒯 i j k

/-- The projection `Tᵢ ×_T Tⱼ ×_T Tₖ → Tⱼ ×_T Tₖ`. -/
def triplePr12 (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ pair 𝒯 j k :=
  pullback.lift (tripleMiddle 𝒯 i j k) (tripleLast 𝒯 i j k) (by
    simp only [tripleMiddle, Category.assoc]
    rw [← pullback.condition]
    simpa only [triple, pairToBase, Category.assoc] using
      (pullback.condition :
        pullback.fst (pairToBase 𝒯 i j) (𝒯.arrow k) ≫ pairToBase 𝒯 i j =
          pullback.snd (pairToBase 𝒯 i j) (𝒯.arrow k) ≫ 𝒯.arrow k))

/-- The projection `Tᵢ ×_T Tⱼ ×_T Tₖ → Tᵢ ×_T Tₖ`. -/
def triplePr02 (i j k : 𝒯.index) : triple 𝒯 i j k ⟶ pair 𝒯 i k :=
  pullback.lift
    (tripleFirst 𝒯 i j k ≫ pairPr0 𝒯 i j)
    (tripleLast 𝒯 i j k) (by
      rw [Category.assoc]
      exact pullback.condition)

end FppfCover

/-- An internal groupoid in the ambient category, with object and arrow
objects over `B`.

Composition is a morphism out of the chosen pullback of target and source.
The generalized-element operation `composeMap` below is the form used by
descent data. -/
structure GroupoidInSpaces (B : C) where
  object : C
  arrow : C
  objectToBase : object ⟶ B
  arrowToBase : arrow ⟶ B
  source : arrow ⟶ object
  target : arrow ⟶ object
  source_over : source ≫ objectToBase = arrowToBase
  target_over : target ≫ objectToBase = arrowToBase
  composition : pullback target source ⟶ arrow
  identity : object ⟶ arrow
  inverse : arrow ⟶ arrow

namespace GroupoidInSpaces

variable {B : C} (G : GroupoidInSpaces B)

/-- Composition of two generalized arrows, in the order first `f`, then `g`. -/
def composeMap {X : C} (f g : X ⟶ G.arrow)
    (h : f ≫ G.target = g ≫ G.source) : X ⟶ G.arrow :=
  pullback.lift f g h ≫ G.composition

/-- The identity arrow at a generalized object. -/
def identityMap {X : C} (f : X ⟶ G.object) : X ⟶ G.arrow :=
  f ≫ G.identity

/-- The inverse of a generalized arrow. -/
def inverseMap {X : C} (f : X ⟶ G.arrow) : X ⟶ G.arrow :=
  f ≫ G.inverse

/- The internal groupoid laws are stated on all generalized elements. -/
class IsGroupoid : Prop where
  identity_source : G.identity ≫ G.source = 𝟙 _
  identity_target : G.identity ≫ G.target = 𝟙 _
  inverse_source : G.inverse ≫ G.source = G.target
  inverse_target : G.inverse ≫ G.target = G.source
  composition_source : ∀ {X : C} (f g : X ⟶ G.arrow)
    (h : f ≫ G.target = g ≫ G.source),
    G.composeMap f g h ≫ G.source = f ≫ G.source
  composition_target : ∀ {X : C} (f g : X ⟶ G.arrow)
    (h : f ≫ G.target = g ≫ G.source),
    G.composeMap f g h ≫ G.target = g ≫ G.target
  left_identity : ∀ {X : C} (f : X ⟶ G.arrow),
    ∃ h : G.identityMap (f ≫ G.source) ≫ G.target = f ≫ G.source,
      G.composeMap (G.identityMap (f ≫ G.source)) f h = f
  right_identity : ∀ {X : C} (f : X ⟶ G.arrow),
    ∃ h : f ≫ G.target = G.identityMap (f ≫ G.target) ≫ G.source,
      G.composeMap f (G.identityMap (f ≫ G.target)) h = f
  inverse_left : ∀ {X : C} (f : X ⟶ G.arrow),
    ∃ h : f ≫ G.target = G.inverseMap f ≫ G.source,
      G.composeMap f (G.inverseMap f) h = G.identityMap (f ≫ G.source)
  inverse_right : ∀ {X : C} (f : X ⟶ G.arrow),
    ∃ h : G.inverseMap f ≫ G.target = f ≫ G.source,
      G.composeMap (G.inverseMap f) f h = G.identityMap (f ≫ G.target)
  associative : ∀ {X : C} (f g h : X ⟶ G.arrow)
    (hfg : f ≫ G.target = g ≫ G.source)
    (hgh : g ≫ G.target = h ≫ G.source),
    ∃ (h₁ : G.composeMap f g hfg ≫ G.target = h ≫ G.source)
      (h₂ : f ≫ G.target = G.composeMap g h hgh ≫ G.source),
      G.composeMap (G.composeMap f g hfg) h h₁ =
        G.composeMap f (G.composeMap g h hgh) h₂

end GroupoidInSpaces

/-- A quotient stack presentation over the site `(C, J)`.

`pointObj` and `pointHom` are the components of the canonical map
`π : 𝒮_U → [U/R]`; `pointPullbackIso` records its compatibility with
pullback. -/
structure QuotientStackData (J : GrothendieckTopology C) (S B : C) where
  baseToS : B ⟶ S
  groupoid : GroupoidInSpaces B
  groupoid_isGroupoid : groupoid.IsGroupoid
  fibered : FiberedCategory.{u, v, w} C
  fibered_isGroupoid : ∀ T : C, CategoryTheory.IsGroupoid (Fiber fibered T)
  isStack : fibered.IsStack J
  pointObj : ∀ {T : C} (_u : T ⟶ groupoid.object), Fiber fibered T
  pointHom : ∀ {T : C} {u v : T ⟶ groupoid.object}
    (r : T ⟶ groupoid.arrow)
    (_source_eq : r ≫ groupoid.source = u)
    (_target_eq : r ≫ groupoid.target = v),
    pointObj u ⟶ pointObj v
  pointPullbackIso : ∀ {X Y : C} (f : X ⟶ Y)
    (u : Y ⟶ groupoid.object),
    (fibered.map f.op.toLoc).toFunctor.obj (pointObj u) ≅
      pointObj (f ≫ u)

namespace QuotientStackData

variable {J : GrothendieckTopology C} {S B : C}
  (Q : Formalization.«Books.SpacesGroupoids».Unit24.QuotientStackData J S B)

/-- Pullback of an object in the quotient-stack fibre. -/
def pullbackObject {X Y : C} (f : X ⟶ Y) (x : Fiber Q.fibered Y) : Fiber Q.fibered X :=
  (Q.fibered.map f.op.toLoc).toFunctor.obj x

/-- Pullback of an isomorphism in the quotient-stack fibre. -/
def pullbackIso {X Y : C} (f : X ⟶ Y) {x y : Fiber Q.fibered Y}
    (e : x ≅ y) : Q.pullbackObject f x ≅ Q.pullbackObject f y :=
  (Q.fibered.map f.op.toLoc).toFunctor.mapIso e

/-- The pseudofunctorial comparison between pullback along a composite and
successive pullback. -/
def pullbackCompIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Fiber Q.fibered Z) :
    Q.pullbackObject (f ≫ g) x ≅ Q.pullbackObject f (Q.pullbackObject g x) :=
  (Cat.Hom.toNatIso
    (Q.fibered.mapComp' g.op.toLoc f.op.toLoc (f ≫ g).op.toLoc (by simp))).app x

/-- Comparison of pullbacks along equal maps. -/
def pullbackObjectEqIso {X Y : C} {f g : X ⟶ Y} (h : f = g)
    (x : Fiber Q.fibered Y) : Q.pullbackObject f x ≅ Q.pullbackObject g x :=
  eqToIso (congrArg (fun q => Q.pullbackObject q x) h)

/-- The canonical isomorphism from a locally trivial point to the pullback of
the global object. -/
def localToBaseChangeIso {X Y Z : C} {x : Fiber Q.fibered Z}
    (q : X ⟶ Y) (f : Y ⟶ Z) (u : Y ⟶ Q.groupoid.object)
    (e : Q.pullbackObject f x ≅ Q.pointObj u) :
    Q.pointObj (q ≫ u) ≅ Q.pullbackObject (q ≫ f) x :=
  (Q.pointPullbackIso q u).symm.trans
    ((Q.pullbackIso q e).symm.trans (Q.pullbackCompIso q f x).symm)

end QuotientStackData

/-- A descent datum with values in the groupoid object `G` over an fppf cover. -/
structure QuotientStackDescentDatum {J : GrothendieckTopology C} {S B : C}
    (G : GroupoidInSpaces B) (baseToS : B ⟶ S)
    {T : SchemeOver S} (𝒯 : FppfCover J T) where
  objectMap : ∀ i, 𝒯.object i ⟶ G.object
  arrowMap : ∀ i j, FppfCover.pair 𝒯 i j ⟶ G.arrow
  object_overS : ∀ i,
    objectMap i ≫ G.objectToBase ≫ baseToS = 𝒯.objectToS i
  arrow_overS : ∀ i j,
    arrowMap i j ≫ G.arrowToBase ≫ baseToS = FppfCover.pairToS 𝒯 i j
  source_eq : ∀ i j,
    arrowMap i j ≫ G.source = FppfCover.pairPr0 𝒯 i j ≫ objectMap i
  target_eq : ∀ i j,
    arrowMap i j ≫ G.target = FppfCover.pairPr1 𝒯 i j ≫ objectMap j
  cocycle : ∀ i j k,
    ∃ h :
        (FppfCover.triplePr01 𝒯 i j k ≫ arrowMap i j) ≫ G.target =
          (FppfCover.triplePr12 𝒯 i j k ≫ arrowMap j k) ≫ G.source,
      G.composeMap
          (FppfCover.triplePr01 𝒯 i j k ≫ arrowMap i j)
          (FppfCover.triplePr12 𝒯 i j k ≫ arrowMap j k) h =
        FppfCover.triplePr02 𝒯 i j k ≫ arrowMap i k

namespace QuotientStackDescentDatum

variable {J : GrothendieckTopology C} {S B : C} {T : SchemeOver S}
  {G : GroupoidInSpaces B} {baseToS : B ⟶ S} {𝒯 : FppfCover J T}

/-- A morphism of descent data, written in the `r_i` notation of the text. -/
@[ext]
structure Hom (D E : QuotientStackDescentDatum G baseToS 𝒯) where
  component : ∀ i, 𝒯.object i ⟶ G.arrow
  overS : ∀ i,
    component i ≫ G.arrowToBase ≫ baseToS = 𝒯.objectToS i
  source_eq : ∀ i, component i ≫ G.source = D.objectMap i
  target_eq : ∀ i, component i ≫ G.target = E.objectMap i
  compatibility : ∀ i j,
    ∃ (h₁ :
        (FppfCover.pairPr0 𝒯 i j ≫ component i) ≫ G.target =
          E.arrowMap i j ≫ G.source)
      (h₂ :
        D.arrowMap i j ≫ G.target =
          (FppfCover.pairPr1 𝒯 i j ≫ component j) ≫ G.source),
      G.composeMap (FppfCover.pairPr0 𝒯 i j ≫ component i)
          (E.arrowMap i j) h₁ =
        G.composeMap (D.arrowMap i j)
          (FppfCover.pairPr1 𝒯 i j ≫ component j) h₂

instance : Category (QuotientStackDescentDatum G baseToS 𝒯) where
  Hom := Hom
  id D :=
    { component := fun i => G.identityMap (D.objectMap i)
      overS := by sorry
      source_eq := by sorry
      target_eq := by sorry
      compatibility := by sorry }
  comp f g :=
    { component := fun i =>
        G.composeMap (f.component i) (g.component i) (by sorry)
      overS := by sorry
      source_eq := by sorry
      target_eq := by sorry
      compatibility := by sorry }

@[simp]
theorem id_component (D : QuotientStackDescentDatum G baseToS 𝒯) (i : 𝒯.index) :
    (𝟙 D : Hom D D).component i = G.identityMap (D.objectMap i) := rfl

@[simp]
theorem comp_component {D E F : QuotientStackDescentDatum G baseToS 𝒯}
    (f : D ⟶ E) (g : E ⟶ F) (i : 𝒯.index) :
    (f ≫ g).component i =
      G.composeMap (f.component i) (g.component i) (by sorry) := rfl

@[ext]
theorem hom_ext {D E : QuotientStackDescentDatum G baseToS 𝒯}
    {f g : D ⟶ E} (h : ∀ i, f.component i = g.component i) : f = g :=
  Hom.ext (funext h)

/-- The source's assertion that the category of descent data is a groupoid. -/
instance [G.IsGroupoid] : IsGroupoid (QuotientStackDescentDatum G baseToS 𝒯) where
  all_isIso := by sorry

end QuotientStackDescentDatum

/-- The groupoid laws of the presenting internal groupoid induce the
groupoid structure on descent data used in the source text. -/
instance quotient_stack_descent_data_isGroupoid
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) {T : SchemeOver S}
    (𝒯 : FppfCover.{t} J T) :
    CategoryTheory.IsGroupoid
      (QuotientStackDescentDatum Q.groupoid Q.baseToS 𝒯) := by
  sorry

/-- A refinement `T'_j → T_{α(j)}` of fppf covers over the same `T`. -/
structure FppfRefinement {J : GrothendieckTopology C} {S : C} {T : SchemeOver S}
    (𝒯 : FppfCover J T) (𝒯' : FppfCover J T) where
  index : 𝒯'.index → 𝒯.index
  leg : ∀ j, 𝒯'.object j ⟶ 𝒯.object (index j)
  commutes : ∀ j, leg j ≫ 𝒯.arrow (index j) = 𝒯'.arrow j

namespace FppfRefinement

variable {J : GrothendieckTopology C} {S : C} {T : SchemeOver S}
  {𝒯 : FppfCover J T} {𝒯' : FppfCover J T}
  (ρ : FppfRefinement 𝒯 𝒯')

/-- The induced map of pairwise fibre products. -/
def pairMap (j j' : 𝒯'.index) :
    FppfCover.pair 𝒯' j j' ⟶ FppfCover.pair 𝒯 (ρ.index j) (ρ.index j') :=
  pullback.lift
    (FppfCover.pairPr0 𝒯' j j' ≫ ρ.leg j)
    (FppfCover.pairPr1 𝒯' j j' ≫ ρ.leg j') (by
      calc
        (FppfCover.pairPr0 𝒯' j j' ≫ ρ.leg j) ≫
            𝒯.arrow (ρ.index j) =
          FppfCover.pairPr0 𝒯' j j' ≫ 𝒯'.arrow j := by
            rw [Category.assoc, ρ.commutes j]
        _ = FppfCover.pairPr1 𝒯' j j' ≫ 𝒯'.arrow j' :=
          (pullback.condition :
            FppfCover.pairPr0 𝒯' j j' ≫ 𝒯'.arrow j =
              FppfCover.pairPr1 𝒯' j j' ≫ 𝒯'.arrow j')
        _ = (FppfCover.pairPr1 𝒯' j j' ≫ ρ.leg j') ≫
            𝒯.arrow (ρ.index j') := by
            rw [Category.assoc, ρ.commutes j'])

end FppfRefinement

/-- Pullback of a groupoid-valued descent datum along a refinement. -/
def pullbackDescentData {J : GrothendieckTopology C} {S B : C} {T : SchemeOver S}
    {G : GroupoidInSpaces B} {baseToS : B ⟶ S}
    {𝒯 : FppfCover J T} {𝒯' : FppfCover J T}
    (ρ : FppfRefinement 𝒯 𝒯') :
    QuotientStackDescentDatum G baseToS 𝒯 ⥤
      QuotientStackDescentDatum G baseToS 𝒯' where
  obj D :=
    { objectMap := fun j => ρ.leg j ≫ D.objectMap (ρ.index j)
      arrowMap := fun j j' =>
        FppfRefinement.pairMap ρ j j' ≫ D.arrowMap (ρ.index j) (ρ.index j')
      object_overS := by sorry
      arrow_overS := by sorry
      source_eq := by sorry
      target_eq := by sorry
      cocycle := by sorry }
  map f :=
    { component := fun j => ρ.leg j ≫ f.component (ρ.index j)
      overS := by sorry
      source_eq := by sorry
      target_eq := by sorry
      compatibility := by sorry }
  map_id := by
    intro D
    apply QuotientStackDescentDatum.hom_ext
    intro j
    sorry
  map_comp := by
    intro D E F f g
    apply QuotientStackDescentDatum.hom_ext
    intro j
    sorry

namespace QuotientStackData

variable {J : GrothendieckTopology C} {S B : C}
  (Q : Formalization.«Books.SpacesGroupoids».Unit24.QuotientStackData J S B)

/-- The displayed transition isomorphism associated to local trivializations
`f_i^*x ≅ π(u_i)`. -/
def localTransitionIso {T : SchemeOver S} (𝒯 : FppfCover J T)
    (x : Fiber Q.fibered T.left)
    (u : ∀ i, 𝒯.object i ⟶ Q.groupoid.object)
    (e : ∀ i, Q.pullbackObject (𝒯.arrow i) x ≅ Q.pointObj (u i))
    (i j : 𝒯.index) :
    Q.pointObj (FppfCover.pairPr0 𝒯 i j ≫ u i) ≅
      Q.pointObj (FppfCover.pairPr1 𝒯 i j ≫ u j) :=
  (Q.localToBaseChangeIso
      (FppfCover.pairPr0 𝒯 i j) (𝒯.arrow i) (u i) (e i)).trans
    ((Q.pullbackObjectEqIso
        (pullback.condition :
          FppfCover.pairPr0 𝒯 i j ≫ 𝒯.arrow i =
            FppfCover.pairPr1 𝒯 i j ≫ 𝒯.arrow j) x).trans
      (Q.localToBaseChangeIso
        (FppfCover.pairPr1 𝒯 i j) (𝒯.arrow j) (u j) (e j)).symm)

end QuotientStackData

/-- A choice of local representatives `u_i` and isomorphisms
`f_i^*x ≅ π(u_i)`. -/
structure QuotientStackLocalTrivialization
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) {T : SchemeOver S}
    (x : Fiber Q.fibered T.left) (𝒯 : FppfCover J T) where
  objectMap : ∀ i, 𝒯.object i ⟶ Q.groupoid.object
  object_overS : ∀ i,
    objectMap i ≫ Q.groupoid.objectToBase ≫ Q.baseToS = 𝒯.objectToS i
  iso : ∀ i, Q.pullbackObject (𝒯.arrow i) x ≅ Q.pointObj (objectMap i)

/-- Transition arrows whose `π`-images are the canonical displayed transition
isomorphisms. -/
structure QuotientStackCanonicalTransition
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) {T : SchemeOver S}
    {x : Fiber Q.fibered T.left} {𝒯 : FppfCover J T}
    (L : QuotientStackLocalTrivialization Q x 𝒯) where
  arrowMap : ∀ i j, FppfCover.pair 𝒯 i j ⟶ Q.groupoid.arrow
  arrow_overS : ∀ i j,
    arrowMap i j ≫ Q.groupoid.arrowToBase ≫ Q.baseToS =
      FppfCover.pairToS 𝒯 i j
  source_eq : ∀ i j,
    arrowMap i j ≫ Q.groupoid.source =
      FppfCover.pairPr0 𝒯 i j ≫ L.objectMap i
  target_eq : ∀ i j,
    arrowMap i j ≫ Q.groupoid.target =
      FppfCover.pairPr1 𝒯 i j ≫ L.objectMap j
  canonical : ∀ i j,
    Q.pointHom (arrowMap i j) (source_eq i j) (target_eq i j) =
      (Q.localTransitionIso 𝒯 x L.objectMap L.iso i j).hom

/-- A local presentation of a quotient-stack object by a descent datum. -/
structure QuotientStackPresentation
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) {T : SchemeOver S}
    (x : Fiber Q.fibered T.left) (𝒯 : FppfCover J T) where
  datum : QuotientStackDescentDatum Q.groupoid Q.baseToS 𝒯
  iso : ∀ i, Q.pullbackObject (𝒯.arrow i) x ≅ Q.pointObj (datum.objectMap i)
  transition : ∀ i j,
    Q.pointHom (datum.arrowMap i j) (datum.source_eq i j) (datum.target_eq i j) =
      (Q.localTransitionIso 𝒯 x datum.objectMap iso i j).hom

namespace QuotientStackPresentationAPI

variable {J : GrothendieckTopology C} {S B : C}
  {Q : QuotientStackData J S B} {T : SchemeOver S}
  {x : Fiber Q.fibered T.left} {𝒯 : FppfCover J T}

/-- Pullback of a local presentation along a refinement. -/
def pullback {𝒯' : FppfCover J T}
    (ρ : FppfRefinement 𝒯 𝒯')
    (P : QuotientStackPresentation Q x 𝒯) :
    QuotientStackPresentation Q x 𝒯' where
  datum := (pullbackDescentData ρ).obj P.datum
  iso := fun j =>
    Q.pullbackObjectEqIso (ρ.commutes j).symm x |>.trans
      (Q.localToBaseChangeIso (ρ.leg j) (𝒯.arrow (ρ.index j))
        (P.datum.objectMap (ρ.index j)) (P.iso (ρ.index j))).symm
  transition := by sorry

end QuotientStackPresentationAPI

/-- The six assertions in the source lemma `lemma-quotient-stack-objects`.

The first three fields separate local triviality, the transition arrows, and
effectivity of their cocycle; the last three record effectivity for arbitrary
descent data, the Hom-bijection, and its refinement compatibility. -/
structure QuotientStackObjectsStatement
    {J : GrothendieckTopology C} {S B : C}
    (Q : QuotientStackData J S B) : Prop where
  local_representability :
    ∀ {T : SchemeOver S} (x : Fiber Q.fibered T.left),
      ∃ (𝒯 : FppfCover.{t} J T),
        Nonempty (QuotientStackLocalTrivialization Q x 𝒯)
  transition_arrows :
    ∀ {T : SchemeOver S} (x : Fiber Q.fibered T.left)
      (𝒯 : FppfCover.{t} J T)
      (L : QuotientStackLocalTrivialization Q x 𝒯),
      Nonempty (QuotientStackCanonicalTransition Q L)
  descent_condition :
    ∀ {T : SchemeOver S} (x : Fiber Q.fibered T.left)
      (𝒯 : FppfCover.{t} J T)
      (L : QuotientStackLocalTrivialization Q x 𝒯)
      (R : QuotientStackCanonicalTransition Q L),
      ∃ D : QuotientStackDescentDatum Q.groupoid Q.baseToS 𝒯,
        D.objectMap = L.objectMap ∧ D.arrowMap = R.arrowMap
  effective :
    ∀ {T : SchemeOver S} (𝒯 : FppfCover.{t} J T)
      (D : QuotientStackDescentDatum Q.groupoid Q.baseToS 𝒯),
        ∃ x : Fiber Q.fibered T.left,
        ∃ P : QuotientStackPresentation Q x 𝒯, P.datum = D
  hom_bijection :
    ∀ {T : SchemeOver S} (x y : Fiber Q.fibered T.left)
      (𝒯 : FppfCover.{t} J T)
      (P : QuotientStackPresentation Q x 𝒯)
      (P' : QuotientStackPresentation Q y 𝒯),
      Nonempty ((x ⟶ y) ≃ (P.datum ⟶ P'.datum))
  refinement_compatibility :
    ∀ {T : SchemeOver S} (x y : Fiber Q.fibered T.left)
      {𝒯 𝒯' : FppfCover.{t} J T}
      (P : QuotientStackPresentation Q x 𝒯)
      (P' : QuotientStackPresentation Q y 𝒯)
      (ρ : FppfRefinement 𝒯 𝒯'),
      ∃ (e : (x ⟶ y) ≃ (P.datum ⟶ P'.datum))
        (e' : (x ⟶ y) ≃
          ((pullbackDescentData ρ).obj P.datum ⟶
            (pullbackDescentData ρ).obj P'.datum)),
        ∀ f, e' f = (pullbackDescentData ρ).map (e f)

end
