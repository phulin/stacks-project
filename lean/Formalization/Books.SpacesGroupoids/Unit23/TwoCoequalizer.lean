import Formalization.«Books.Stacks».Unit01.Foundation
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Groupoids in Algebraic Spaces, Chapter 23: the 2-coequalizer property

The source uses the quotient-stack diagram constructed in the preceding
sections.  The interface below records exactly the part of that construction
used in this chapter: the three objects associated to `U`, `R`, and
`R × U R`, the quotient stack, the structure maps, and the canonical
2-morphism.  The geometric construction is deliberately kept behind this
interface, since Mathlib and the earlier formalization do not provide a type
of algebraic spaces.
-/

universe w v u

open CategoryTheory
open CategoryTheory.Bicategory
open CategoryTheory.Pseudofunctor
open Opposite
open Formalization.«Books.Stacks».Unit01

open scoped CategoryTheory.Pseudofunctor.StrongTrans

namespace Formalization.«Books.SpacesGroupoids».Unit23

variable {C : Type u} [Category.{v} C]

/-!
## The quotient-stack diagram
-/

/-- A chosen 2-morphism between morphisms of stacks presented by pseudofunctors. -/
abbrev StackTwoMorphism {F G : FiberedCategory.{w, v, u} C} (f g : F ⟶ G) := f ⟶ g

/-- Transport a 2-morphism along equalities of its source and target 1-morphisms. -/
def transportTwoMorphism {F G : FiberedCategory.{w, v, u} C}
    {f f' g g' : F ⟶ G}
    (source : f = g) (target : f' = g')
    (α : StackTwoMorphism f f') : StackTwoMorphism g g' :=
  eqToHom source.symm ≫ α ≫ eqToHom target

/-- Compose 2-morphisms whose middle 1-morphisms are propositionally equal. -/
def verticalComposeAlongEq {F G : FiberedCategory.{w, v, u} C}
    {f₀ f₁ f₁' f₂ : F ⟶ G} (middle : f₁ = f₁')
    (α : StackTwoMorphism f₀ f₁)
    (β : StackTwoMorphism f₁' f₂) : StackTwoMorphism f₀ f₂ :=
  α ≫ eqToHom middle ≫ β

/--
The stack-level data supplied by the quotient-stack construction.

Here `R2` denotes `R ×_{s,U,t} R`, and `pr₁`, `pr₀`, and `c` denote the two
projections and composition.  The fields `source_eq`, `middle_eq`, and
`target_eq` are the three equalities stated immediately before the first
lemma in the source.  They are kept as fields because they are needed to
type the vertical composition of the whiskered 2-morphisms.
-/
structure QuotientStackDiagram (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  U : FiberedCategory.{w, v, u} C
  R : FiberedCategory.{w, v, u} C
  R2 : FiberedCategory.{w, v, u} C
  Q : FiberedCategory.{w, v, u} C
  U_isStackInSets : FiberwiseSet U ∧ Stack U J
  R_isStackInSets : FiberwiseSet R ∧ Stack R J
  R2_isStackInSets : FiberwiseSet R2 ∧ Stack R2 J
  Q_isStackInGroupoids : FiberwiseGroupoid Q ∧ Stack Q J
  s : R ⟶ U
  t : R ⟶ U
  pr₁ : R2 ⟶ R
  pr₀ : R2 ⟶ R
  c : R2 ⟶ R
  π : U ⟶ Q
  source_eq : pr₁ ≫ s = c ≫ s
  middle_eq : pr₁ ≫ t = pr₀ ≫ s
  target_eq : pr₀ ≫ t = c ≫ t
  alpha : StackTwoMorphism (s ≫ π) (t ≫ π)

/-!
## The cocycle equation
-/

/--
Whisker a 2-morphism along one of the maps `R2 ⟶ R`, with the
associators made explicit so that the result is parenthesized as
`(p ≫ s) ≫ f` and `(p ≫ t) ≫ f`.
-/
def whiskeredTwoMorphism (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (p : D.R2 ⟶ D.R)
    (f : D.U ⟶ X)
    (β : StackTwoMorphism (D.s ≫ f) (D.t ≫ f)) :
    StackTwoMorphism ((p ≫ D.s) ≫ f) ((p ≫ D.t) ≫ f) :=
  (Bicategory.associator p D.s f).hom ≫
    Bicategory.whiskerLeft p β ≫
    (Bicategory.associator p D.t f).inv

/--
The composite of the two whiskered 2-morphisms along `pr₁` and `pr₀`, with
the middle equality inserted explicitly.  This is the right-hand side of
the cocycle equation in both lemmas of the source.
-/
def cocycleComposite (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (f : D.U ⟶ X)
    (β : StackTwoMorphism (D.s ≫ f) (D.t ≫ f)) :
    StackTwoMorphism ((D.c ≫ D.s) ≫ f) ((D.c ≫ D.t) ≫ f) :=
  transportTwoMorphism
    (congrArg (fun q : D.R2 ⟶ D.U => q ≫ f) D.source_eq)
    (congrArg (fun q : D.R2 ⟶ D.U => q ≫ f) D.target_eq)
    (verticalComposeAlongEq
      (congrArg (fun q : D.R2 ⟶ D.U => q ≫ f) D.middle_eq)
      (whiskeredTwoMorphism D D.pr₁ f β)
      (whiskeredTwoMorphism D D.pr₀ f β))

/-- The cocycle condition for a 2-morphism over the groupoid composition. -/
def SatisfiesCocycle (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (f : D.U ⟶ X)
    (β : StackTwoMorphism (D.s ≫ f) (D.t ≫ f)) : Prop :=
  whiskeredTwoMorphism D D.c f β = cocycleComposite D f β

/--
The canonical 2-morphism of the quotient-stack square satisfies the cocycle
condition induced by composition in `R`.
-/
theorem quotient_stack_cocycle (D : QuotientStackDiagram C J) :
    SatisfiesCocycle D D.π D.alpha := by
  sorry

/-!
## 2-commutative factorization
-/

/--
The 2-morphism from `s ≫ f` to `t ≫ f` induced by a factorization
2-isomorphism `π ≫ g ≅ f` and the canonical quotient-stack 2-morphism.
Associators are included explicitly so this is a well-typed bicategorical
composite.
-/
def inducedCocycleMorphism (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (f : D.U ⟶ X) (g : D.Q ⟶ X)
    (γ : (D.π ≫ g) ≅ f) :
    StackTwoMorphism (D.s ≫ f) (D.t ≫ f) :=
  Bicategory.whiskerLeft D.s γ.inv ≫
    (Bicategory.associator D.s D.π g).inv ≫
    Bicategory.whiskerRight D.alpha g ≫
    (Bicategory.associator D.t D.π g).hom ≫
    Bicategory.whiskerLeft D.t γ.hom

/--
`g` makes the quotient-stack diagram 2-commute with the given `f` and `β`.
The isomorphism `γ` is the lower triangular 2-commutativity datum, and the
second field says that the resulting boundary 2-morphism is exactly `β`.
-/
def MakesDiagramTwoCommute (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (f : D.U ⟶ X)
    (β : StackTwoMorphism (D.s ≫ f) (D.t ≫ f))
    (g : D.Q ⟶ X) : Prop :=
  ∃ γ : (D.π ≫ g) ≅ f, β = inducedCocycleMorphism D f g γ

/-!
## The 2-coequalizer property
-/

/--
The quotient-stack square is a 2-coequalizer: a cocycle-compatible map out
of `U` extends to the quotient stack, with the prescribed 2-commutativity.
-/
theorem quotient_stack_two_coequalizer (D : QuotientStackDiagram C J)
    {X : FiberedCategory.{w, v, u} C} (hX : FiberwiseGroupoid X ∧ Stack X J)
    (f : D.U ⟶ X)
    (β : StackTwoMorphism (D.s ≫ f) (D.t ≫ f))
    (hβ : SatisfiesCocycle D f β) :
    ∃ g : D.Q ⟶ X, MakesDiagramTwoCommute D f β g := by
  sorry

end Formalization.«Books.SpacesGroupoids».Unit23
