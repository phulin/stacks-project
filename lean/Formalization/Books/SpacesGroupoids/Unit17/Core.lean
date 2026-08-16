import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Groupoids in Algebraic Spaces, Chapter 17: shared interfaces

The algebraic-space library is not part of the Mathlib version used by this
project.  The chapter therefore uses the same categorical interface as the
existing algebraic-space formalization: `TopCat` supplies the ambient category
and `Over` supplies spaces over a base.  All groupoid and relation data below
are internal to the resulting category, so the pullback formulas are the
source-faithful formulas for algebraic spaces over a base.
-/

namespace Formalization.Books.SpacesGroupoids.Unit17

open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

/-- The ambient categorical model for algebraic spaces in this project. -/
abbrev AlgebraicSpace := TopCat

/-- Algebraic spaces over an ambient algebraic space. -/
abbrev AlgebraicSpaceOver (S : AlgebraicSpace) := Over S

/-- Algebraic spaces over `B`, where `B` is itself over `S`. -/
abbrev AlgebraicSpaceOverB {S : AlgebraicSpace} (B : AlgebraicSpaceOver S) := Over B

/-- The raw structure underlying a groupoid in algebraic spaces.

The order of the arguments to `c` follows the book: a composable pair
`(r₁, r₂)` satisfies `s r₁ = t r₂`, and its composite has source `s r₂`
and target `t r₁`.
-/
structure GroupoidData (S : AlgebraicSpace) (B : AlgebraicSpaceOver S) where
  U : AlgebraicSpaceOverB B
  R : AlgebraicSpaceOverB B
  s : R ⟶ U
  t : R ⟶ U
  c : pullback s t ⟶ R
  e : U ⟶ R
  i : R ⟶ R

namespace GroupoidData

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}

/-- The object of composable pairs of arrows. -/
abbrev composable (D : GroupoidData S B) := pullback D.s D.t

/-- The object of composable triples of arrows. -/
abbrev composableTriple (D : GroupoidData S B) :=
  pullback (pullback.snd D.s D.t ≫ D.s) D.t

/-- The first arrow in a composable pair. -/
abbrev first (D : GroupoidData S B) : D.composable ⟶ D.R :=
  pullback.fst D.s D.t

/-- The second arrow in a composable pair. -/
abbrev second (D : GroupoidData S B) : D.composable ⟶ D.R :=
  pullback.snd D.s D.t

/-- The pair `(r, e(s(r)))`. -/
noncomputable def leftUnitPair (D : GroupoidData S B)
    (h : D.e ≫ D.t = 𝟙 D.U) : D.R ⟶ D.composable :=
  pullback.lift (𝟙 D.R) (D.s ≫ D.e) (by
    rw [Category.id_comp, Category.assoc, h, Category.comp_id])

/-- The pair `(e(t(r)), r)`. -/
noncomputable def rightUnitPair (D : GroupoidData S B)
    (h : D.e ≫ D.s = 𝟙 D.U) : D.R ⟶ D.composable :=
  pullback.lift (D.t ≫ D.e) (𝟙 D.R) (by
    rw [Category.assoc, h, Category.id_comp, Category.comp_id])

/-- The pair `(r, i(r))`. -/
noncomputable def rightInversePair (D : GroupoidData S B)
    (h : D.i ≫ D.t = D.s) : D.R ⟶ D.composable :=
  pullback.lift (𝟙 D.R) D.i (by
    rw [Category.id_comp, h])

/-- The pair `(i(r), r)`. -/
noncomputable def leftInversePair (D : GroupoidData S B)
    (h : D.i ≫ D.s = D.t) : D.R ⟶ D.composable :=
  pullback.lift D.i (𝟙 D.R) (by
    rw [h, Category.id_comp])

section Associativity

variable (D : GroupoidData S B)

private abbrev tripleFirst : D.composableTriple ⟶ D.composable :=
  pullback.fst (pullback.snd D.s D.t ≫ D.s) D.t

private abbrev tripleThird : D.composableTriple ⟶ D.R :=
  pullback.snd (pullback.snd D.s D.t ≫ D.s) D.t

/-- The pair `(r₂, r₃)` in a composable triple. -/
noncomputable def tripleInnerPair : D.composableTriple ⟶ D.composable :=
  pullback.lift
    (tripleFirst D ≫ second D)
    (tripleThird D)
    (by
      simpa [Category.assoc] using
        (pullback.condition :
          tripleFirst D ≫ (pullback.snd D.s D.t ≫ D.s) =
            tripleThird D ≫ D.t))

/-- The pair `(r₁, c(r₂,r₃))`. -/
noncomputable def tripleRightPair
    (_h₁ : D.c ≫ D.s = second D ≫ D.s)
    (h₂ : D.c ≫ D.t = first D ≫ D.t) :
    D.composableTriple ⟶ D.composable :=
  pullback.lift
    (tripleFirst D ≫ first D)
    (tripleInnerPair D ≫ D.c)
    (by
      calc
        (tripleFirst D ≫ first D) ≫ D.s =
            tripleFirst D ≫ (first D ≫ D.s) := by simp [Category.assoc]
        _ = tripleFirst D ≫ (second D ≫ D.t) := by rw [pullback.condition]
        _ = (tripleFirst D ≫ second D) ≫ D.t := by simp [Category.assoc]
        _ = (tripleInnerPair D ≫ first D) ≫ D.t := by
              have hfirst : tripleInnerPair D ≫ first D =
                  tripleFirst D ≫ second D := by
                dsimp [tripleInnerPair, first, second]
                exact pullback.lift_fst _ _ _
              rw [hfirst]
        _ = (tripleInnerPair D ≫ D.c) ≫ D.t := by
              simpa [Category.assoc] using
                congrArg (fun q => tripleInnerPair D ≫ q) h₂.symm)

/-- The pair `(c(r₁,r₂), r₃)`. -/
noncomputable def tripleLeftPair
    (h₁ : D.c ≫ D.s = second D ≫ D.s)
    (_h₂ : D.c ≫ D.t = first D ≫ D.t) :
    D.composableTriple ⟶ D.composable :=
  pullback.lift
    (tripleFirst D ≫ D.c)
    (tripleThird D)
    (by
      simp only [Category.assoc]
      rw [h₁]
      simpa [Category.assoc] using
        (pullback.condition :
          tripleFirst D ≫ (pullback.snd D.s D.t ≫ D.s) =
            tripleThird D ≫ D.t))

/-- The two composites of a composable triple, with the left association. -/
noncomputable def associativityLeft
    (h₁ : D.c ≫ D.s = second D ≫ D.s)
    (h₂ : D.c ≫ D.t = first D ≫ D.t) :
    D.composableTriple ⟶ D.R :=
  tripleLeftPair D h₁ h₂ ≫ D.c

/-- The two composites of a composable triple, with the right association. -/
noncomputable def associativityRight
    (h₁ : D.c ≫ D.s = second D ≫ D.s)
    (h₂ : D.c ≫ D.t = first D ≫ D.t) :
    D.composableTriple ⟶ D.R :=
  tripleRightPair D h₁ h₂ ≫ D.c

end Associativity

end GroupoidData

/-- The internal groupoid axioms for the raw data.

This is the categorical form of the pointwise groupoid axioms used in the
source.  The chosen pullbacks make every displayed identity an equality of
morphisms in the category of spaces over `B`.
-/
structure GroupoidAxioms {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}
    (D : GroupoidData S B) : Prop where
  source_comp : D.c ≫ D.s = D.second ≫ D.s
  target_comp : D.c ≫ D.t = D.first ≫ D.t
  source_identity : D.e ≫ D.s = 𝟙 D.U
  target_identity : D.e ≫ D.t = 𝟙 D.U
  source_inverse : D.i ≫ D.s = D.t
  target_inverse : D.i ≫ D.t = D.s
  left_identity : D.leftUnitPair target_identity ≫ D.c = 𝟙 D.R
  right_identity : D.rightUnitPair source_identity ≫ D.c = 𝟙 D.R
  right_inverse : D.rightInversePair target_inverse ≫ D.c = D.t ≫ D.e
  left_inverse : D.leftInversePair source_inverse ≫ D.c = D.s ≫ D.e
  associativity :
    D.associativityLeft source_comp target_comp =
      D.associativityRight source_comp target_comp

/-- A groupoid in algebraic spaces over `B`. -/
structure GroupoidInAlgebraicSpaces (S : AlgebraicSpace)
    (B : AlgebraicSpaceOver S) extends GroupoidData S B where
  axioms : GroupoidAxioms toGroupoidData

namespace GroupoidInAlgebraicSpaces

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}

/-- The raw data of a groupoid. -/
abbrev data (G : GroupoidInAlgebraicSpaces S B) : GroupoidData S B :=
  G.toGroupoidData

/-- The source map of a groupoid. -/
abbrev source (G : GroupoidInAlgebraicSpaces S B) := G.data.s

/-- The target map of a groupoid. -/
abbrev target (G : GroupoidInAlgebraicSpaces S B) := G.data.t

/-- The composition law of a groupoid. -/
abbrev composition (G : GroupoidInAlgebraicSpaces S B) := G.data.c

/-- The identity section of a groupoid. -/
abbrev identity (G : GroupoidInAlgebraicSpaces S B) := G.data.e

/-- The inverse map of a groupoid. -/
abbrev inverse (G : GroupoidInAlgebraicSpaces S B) := G.data.i

/-- The object space of a groupoid. -/
abbrev objectSpace (G : GroupoidInAlgebraicSpaces S B) := G.data.U

/-- The arrow space of a groupoid. -/
abbrev arrowSpace (G : GroupoidInAlgebraicSpaces S B) := G.data.R

/-- The composable-arrow space of a groupoid. -/
abbrev composable (G : GroupoidInAlgebraicSpaces S B) := G.data.composable

/-- The first projection from the composable-arrow space. -/
abbrev composableFst (G : GroupoidInAlgebraicSpaces S B) :
    G.composable ⟶ G.arrowSpace := G.data.first

/-- The second projection from the composable-arrow space. -/
abbrev composableSnd (G : GroupoidInAlgebraicSpaces S B) :
    G.composable ⟶ G.arrowSpace := G.data.second

end GroupoidInAlgebraicSpaces

/-- The source and target data underlying a pre-equivalence relation. -/
structure AlgebraicSpaceRelation (S : AlgebraicSpace)
    (B : AlgebraicSpaceOver S) (U : AlgebraicSpaceOverB B) where
  arrows : AlgebraicSpaceOverB B
  source : arrows ⟶ U
  target : arrows ⟶ U

namespace AlgebraicSpaceRelation

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}

/-- The terminal object of the category of spaces over `B`. -/
abbrev overTerminal : AlgebraicSpaceOverB B := Over.mk (𝟙 B)

/-- The unique structure morphism from a space over `B` to the terminal
object of the over-category. -/
noncomputable def terminalMap (X : AlgebraicSpaceOverB B) :
    X ⟶ overTerminal :=
  Over.homMk X.hom (by simp)

/-- The fibre product `X ×_B Y`, represented as a product in `Over B`. -/
abbrev overProduct (X Y : AlgebraicSpaceOverB B) :=
  pullback (terminalMap X) (terminalMap Y)

/-- The map `j = (t,s) : R → U ×_B U` attached to relation data. -/
noncomputable def map {U : AlgebraicSpaceOverB B}
    (Q : AlgebraicSpaceRelation S B U) :
    Q.arrows ⟶ overProduct U U :=
  pullback.lift Q.target Q.source (by
    apply Over.OverMorphism.ext
    simp [terminalMap])

/-- The relation on `T`-valued points represented by `Q`. -/
def Related {U : AlgebraicSpaceOverB B}
    (Q : AlgebraicSpaceRelation S B U) (T : AlgebraicSpaceOverB B)
    (x y : T ⟶ U) : Prop :=
  ∃ r : T ⟶ Q.arrows, r ≫ Q.target = x ∧ r ≫ Q.source = y

/-- A relation map is a monomorphism. -/
def IsRelation {U : AlgebraicSpaceOverB B}
    (Q : AlgebraicSpaceRelation S B U) : Prop :=
  ∀ {T : AlgebraicSpaceOverB B} (f₁ f₂ : T ⟶ Q.arrows),
    f₁ ≫ Q.map = f₂ ≫ Q.map → f₁ = f₂

/-- Pointwise equivalence of the relation represented by `Q`. -/
def IsPreEquivalenceRelation {U : AlgebraicSpaceOverB B}
    (Q : AlgebraicSpaceRelation S B U) : Prop :=
  ∀ T : AlgebraicSpaceOverB B, Equivalence (Q.Related T)

/-- An equivalence relation is a pre-equivalence relation whose relation map
is a monomorphism. -/
def IsEquivalenceRelation {U : AlgebraicSpaceOverB B}
    (Q : AlgebraicSpaceRelation S B U) : Prop :=
  IsPreEquivalenceRelation Q ∧ IsRelation Q

end AlgebraicSpaceRelation

namespace GroupoidInAlgebraicSpaces

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}

/-- The relation underlying a groupoid. -/
def toRelation (G : GroupoidInAlgebraicSpaces S B) :
    AlgebraicSpaceRelation S B G.objectSpace where
  arrows := G.arrowSpace
  source := G.source
  target := G.target

end GroupoidInAlgebraicSpaces

/-- A morphism of internal groupoid data before imposing compatibility with
composition. -/
structure GroupoidMorphismCore {S : AlgebraicSpace}
    {B : AlgebraicSpaceOver S}
    (G H : GroupoidInAlgebraicSpaces S B) where
  object : G.objectSpace ⟶ H.objectSpace
  arrow : G.arrowSpace ⟶ H.arrowSpace
  source_commutes : arrow ≫ H.source = G.source ≫ object
  target_commutes : arrow ≫ H.target = G.target ≫ object

namespace GroupoidMorphismCore

variable {S : AlgebraicSpace} {B : AlgebraicSpaceOver S}
variable {G H : GroupoidInAlgebraicSpaces S B}

/-- The induced map on composable pairs. -/
noncomputable def mapComposable (F : GroupoidMorphismCore G H) :
    G.composable ⟶ H.composable :=
  pullback.lift
    (G.composableFst ≫ F.arrow)
    (G.composableSnd ≫ F.arrow)
    (by
      simp only [Category.assoc]
      rw [F.source_commutes, F.target_commutes]
      exact congrArg (fun q => q ≫ F.object)
        (pullback.condition :
          G.composableFst ≫ G.source = G.composableSnd ≫ G.target))

end GroupoidMorphismCore

/-- A morphism of groupoids in algebraic spaces. -/
structure GroupoidMorphism {S : AlgebraicSpace}
    {B : AlgebraicSpaceOver S}
    (G H : GroupoidInAlgebraicSpaces S B)
    extends GroupoidMorphismCore G H where
  composition_commutes : toGroupoidMorphismCore.mapComposable ≫ H.composition =
    G.composition ≫ arrow

end

end Formalization.Books.SpacesGroupoids.Unit17
