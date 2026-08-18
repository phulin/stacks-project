import Formalization.Books.Stacks.Unit04.Stacks

/-!
# A Guide to the Literature, Chapter 2: stack interfaces

The source chapter uses the standard notions of representable diagonal and of
an étale or smooth presentation by schemes.  The project already provides
`StackObject` and `StackMorphism`, but it does not yet provide a category of
algebraic stacks or its products.  This file supplies only the small
presentation-level interface needed to state those notions faithfully.
-/

namespace Formalization.Books.Guide.Unit02

open CategoryTheory
open Formalization.Books.Stacks.Unit01
open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe u v w

/-! ## Stack morphisms and products -/

/-- Identity morphism in the presentation-level interface for stacks. -/
def stackMorphismId {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (X : StackObject.{w, v, u} C J) :
    StackMorphism.{v, u, w} X X where
  map := 𝟙 X.value

/-- Composition of stack morphisms in the presentation-level interface. -/
def stackMorphismComp {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {X Y Z : StackObject.{w, v, u} C J}
    (f : StackMorphism.{v, u, w} X Y)
    (g : StackMorphism.{v, u, w} Y Z) :
    StackMorphism.{v, u, w} X Z where
  map := f.map ≫ g.map

/-- Isomorphism of stack morphisms, expressed in the existing 2-morphism
category of strong transformations. -/
def StackMorphism2Iso {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    {X Y : StackObject.{w, v, u} C J}
    (f g : StackMorphism.{v, u, w} X Y) : Prop :=
  Nonempty (f.map ≅ g.map)

/-- A product of two stack objects up to 2-isomorphism, including the
object-level universal property needed here.  The project has no ambient
category of stacks, so this is recorded directly at the level of the existing
morphism interface. -/
structure StackProduct {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (X Y : StackObject.{w, v, u} C J) where
  product : StackObject.{w, v, u} C J
  fst : StackMorphism.{v, u, w} product X
  snd : StackMorphism.{v, u, w} product Y
  isProduct : ∀ (Z : StackObject.{w, v, u} C J)
    (f : StackMorphism.{v, u, w} Z X)
    (g : StackMorphism.{v, u, w} Z Y),
    ∃ h : StackMorphism.{v, u, w} Z product,
      StackMorphism2Iso (stackMorphismComp h fst) f ∧
        StackMorphism2Iso (stackMorphismComp h snd) g ∧
        ∀ h' : StackMorphism.{v, u, w} Z product,
          StackMorphism2Iso (stackMorphismComp h' fst) f →
          StackMorphism2Iso (stackMorphismComp h' snd) g →
          StackMorphism2Iso h h'

/-! ## The geometric data used by the source definitions -/

/-- The geometric predicates required to talk about algebraic stacks over a
site.  `representable` is the stack attached to a scheme object, while the
four morphism predicates are the standard geometric properties appearing in
the source definitions. -/
structure StackSite (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  isScheme : C → Prop
  representable : ∀ (U : C), isScheme U → StackObject.{w, v, u} C J
  isRepresentableByAlgebraicSpace :
    ∀ {X Y : StackObject.{w, v, u} C J},
      StackMorphism.{v, u, w} X Y → Prop
  isEtale : ∀ {X Y : StackObject.{w, v, u} C J},
    StackMorphism.{v, u, w} X Y → Prop
  isSmooth : ∀ {X Y : StackObject.{w, v, u} C J},
    StackMorphism.{v, u, w} X Y → Prop
  isSurjective : ∀ {X Y : StackObject.{w, v, u} C J},
    StackMorphism.{v, u, w} X Y → Prop
  product : ∀ (X Y : StackObject.{w, v, u} C J), StackProduct X Y
  etaleImpliesSmooth : ∀ {X Y : StackObject.{w, v, u} C J}
    (f : StackMorphism.{v, u, w} X Y), isEtale f → isSmooth f

/-- The diagonal of a stack object, obtained from the universal property of
the chosen self-product. -/
noncomputable def stackDiagonal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) :
    StackMorphism.{v, u, w} X (S.product X X).product :=
  Classical.choose
    ((S.product X X).isProduct X (stackMorphismId X) (stackMorphismId X))

/-- A scheme presentation of a stack object, with its covering map recorded
but without yet specifying whether that map is étale or smooth. -/
structure StackPresentation {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) where
  scheme : C
  scheme_isScheme : S.isScheme scheme
  map : StackMorphism.{v, u, w} (S.representable scheme scheme_isScheme) X
  map_isSurjective : S.isSurjective map

/-- The two projection laws that characterize a diagonal map into the chosen
self-product. -/
def IsStackDiagonal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J)
    (d : StackMorphism.{v, u, w} X (S.product X X).product) : Prop :=
  StackMorphism2Iso (stackMorphismComp d (S.product X X).fst) (stackMorphismId X) ∧
    StackMorphism2Iso (stackMorphismComp d (S.product X X).snd) (stackMorphismId X)

/-- The source condition that the diagonal be representable by an algebraic
space. -/
def HasRepresentableDiagonal {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) : Prop :=
  ∃ d : StackMorphism.{v, u, w} X (S.product X X).product,
    IsStackDiagonal S X d ∧ S.isRepresentableByAlgebraicSpace d

/-- Existence of a scheme presentation whose map is étale. -/
def HasEtalePresentation {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) : Prop :=
  ∃ P : StackPresentation S X, S.isEtale P.map

/-- Existence of a scheme presentation whose map is smooth. -/
def HasSmoothPresentation {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) : Prop :=
  ∃ P : StackPresentation S X, S.isSmooth P.map

/-- The definition used in the Deligne--Mumford reference: a stack with
representable diagonal and an étale presentation by schemes. -/
def IsDeligneMumfordStack {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) : Prop :=
  HasRepresentableDiagonal S X ∧ HasEtalePresentation S X

/-- The definition used in the Artin reference: a stack with representable
diagonal and a smooth presentation by schemes. -/
def IsArtinStack {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (S : StackSite.{u, v, w} C J)
    (X : StackObject.{w, v, u} C J) : Prop :=
  HasRepresentableDiagonal S X ∧ HasSmoothPresentation S X

end Formalization.Books.Guide.Unit02
