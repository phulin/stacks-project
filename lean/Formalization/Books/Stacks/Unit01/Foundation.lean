import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Stacks, Chapter 1: shared interfaces

Mathlib's descent library presents a fibred category by a pseudofunctor to
`Cat`.  The chapter files use that established presentation directly.
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Opposite

open scoped CategoryTheory.Pseudofunctor.StrongTrans

universe t w v u

variable {C : Type u} [Category.{v} C]

abbrev FiberedCategory (C : Type u) [Category.{v} C] :=
  Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}

abbrev Fiber (F : FiberedCategory C) (U : C) := F.obj (.mk (op U))

abbrev Over (C : Type u) [Category.{v} C] (U : C) := CategoryTheory.Over U

abbrev MorPresheaf (F : FiberedCategory C) {U : C}
    (x y : Fiber F U) : (Over C U)ᵒᵖ ⥤ Type w :=
  F.presheafHom x y

abbrev IsomSection (F : FiberedCategory C) {U : C} (x y : Fiber F U)
    (T : (Over C U)ᵒᵖ) := { f : (F.presheafHom x y).obj T // IsIso f }

def IsomPresheaf (F : FiberedCategory C) {U : C} (x y : Fiber F U) :
    (Over C U)ᵒᵖ ⥤ Type w where
  obj T := IsomSection F x y T
  map {T₁ T₂} q := ↾fun (f : { f : (F.presheafHom x y).obj T₁ // IsIso f }) =>
      (⟨(F.presheafHom x y).map q f.1, by
        rcases f.property.out with ⟨g, h₁, h₂⟩
        let g' : (F.presheafHom y x).obj T₁ := by
          simpa [Pseudofunctor.presheafHom] using g
        refine ⟨(F.presheafHom y x).map q g', ?_, ?_⟩
        · simpa [g', Pseudofunctor.presheafHom,
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
            congrArg (fun h => (F.presheafHom x x).map q h) h₁
        · simpa [g', Pseudofunctor.presheafHom,
            Pseudofunctor.LocallyDiscreteOpToCat.pullHom] using
            congrArg (fun h => (F.presheafHom y y).map q h) h₂⟩ :
        { f : (F.presheafHom x y).obj T₂ // IsIso f })

abbrev DescentData (F : FiberedCategory C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) := F.DescentData f

def EffectiveDescentData (F : FiberedCategory C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) (D : F.DescentData f) : Prop :=
  ∃ M, Nonempty ((F.toDescentData f).obj M ≅ D)

def CoveringFamily (J : GrothendieckTopology C) {ι : Type t} {U : C}
    {X : ι → C} (f : ∀ i, X i ⟶ U) : Prop :=
  Sieve.ofArrows X f ∈ J U

abbrev Prestack (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  F.IsPrestack J

abbrev Stack (F : FiberedCategory C) (J : GrothendieckTopology C) : Prop :=
  F.IsStack J

def FiberwiseGroupoid (F : FiberedCategory C) : Prop :=
  ∀ U : C, IsGroupoid (Fiber F U)

def FiberwiseSetoid (F : FiberedCategory C) : Prop :=
  FiberwiseGroupoid F ∧
    ∀ (U : C) (X Y : Fiber F U), Subsingleton (X ⟶ Y)

def FiberwiseSet (F : FiberedCategory C) : Prop :=
  ∀ U : C, IsDiscrete (Fiber F U)

abbrev FiberedMorphism (F G : FiberedCategory C) := F ⟶ G

def FiberwiseFullyFaithful {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, Nonempty (η.app (.mk (op U))).toFunctor.FullyFaithful

def FiberwiseEssentiallySurjective {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  ∀ U : C, (η.app (.mk (op U))).toFunctor.EssSurj

def FiberwiseEquivalence {F G : FiberedCategory C}
    (η : FiberedMorphism F G) : Prop :=
  FiberwiseFullyFaithful η ∧ FiberwiseEssentiallySurjective η

/- TODO(stacks-foundation): Before retrying the stack-preservation results, prove a
single transport lemma saying that a `FiberwiseEquivalence` induces an
equivalence between the two descent-data categories for every family.  Build
the functor from the strong transformation `η`; use fibrewise full faithfulness
for morphisms and fibrewise essential surjectivity, together with the
pseudonaturality isomorphisms, to descend the gluing data.  The later
`equivalent_*_preserve` theorems should be short consequences of this lemma. -/

structure Substack (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  inclusion : FiberedMorphism value F
  fullyFaithful : FiberwiseFullyFaithful inclusion
  stableUnderPullback : ∀ {U V : C} (f : V ⟶ U) (x : Fiber value U),
    ∃ y : Fiber value V,
      Nonempty (y ≅ (value.map f.op.toLoc).toFunctor.obj x)
  locallyEssentiallyInImage : ∀ (U : C) (x : Fiber F U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ y : Fiber value (X i),
          Nonempty ((F.map (f i).op.toLoc).toFunctor.obj x ≅
            (inclusion.app (.mk (op (X i)))).toFunctor.obj y)

def IsTwoPullbackCone {F G H A : FiberedCategory C}
    (f : FiberedMorphism F H) (g : FiberedMorphism G H)
    (left : FiberedMorphism A F) (right : FiberedMorphism A G)
    (commutes : left ≫ f ≅ right ≫ g) : Prop :=
  ∀ (Q : FiberedCategory C) (a : FiberedMorphism Q F)
      (b : FiberedMorphism Q G) (α : a ≫ f ≅ b ≫ g),
    ∃ (u : FiberedMorphism Q A) (lam : u ≫ left ≅ a)
      (rho : u ≫ right ≅ b),
      (Bicategory.whiskerRight lam.hom f) ≫ α.hom =
          (Bicategory.associator u left f).hom ≫
            Bicategory.whiskerLeft u commutes.hom ≫
              (Bicategory.associator u right g).inv ≫
                (Bicategory.whiskerRight rho.hom g) ∧
        ∀ (v : FiberedMorphism Q A) (lam' : v ≫ left ≅ a)
          (rho' : v ≫ right ≅ b),
          (Bicategory.whiskerRight lam'.hom f) ≫ α.hom =
              (Bicategory.associator v left f).hom ≫
                Bicategory.whiskerLeft v commutes.hom ≫
                  (Bicategory.associator v right g).inv ≫
                    (Bicategory.whiskerRight rho'.hom g) →
            ∃! β : u ⟶ v,
              (Bicategory.whiskerRight β left) ≫ lam'.hom = lam.hom ∧
                (Bicategory.whiskerRight β right) ≫ rho'.hom = rho.hom

structure TwoFiberProductCone (F G H : FiberedCategory C)
    (f : FiberedMorphism F H) (g : FiberedMorphism G H) where
  apex : FiberedCategory C
  left : FiberedMorphism apex F
  right : FiberedMorphism apex G
  commutes : left ≫ f ≅ right ≫ g
  isTwoPullback : IsTwoPullbackCone f g left right commutes

/- TODO(stacks-foundation): Construct the reusable cone above pointwise as the
iso-comma category of `f.app U` and `g.app U`.  Reindexing is componentwise,
with the strong-transformation coherence isomorphisms supplying the comparison
arrow.  First prove the pointwise universal property, then package it as
`IsTwoPullbackCone`; stack/groupoid/setoid closure should depend on that one
construction instead of rebuilding a cone in each downstream theorem. -/

def IsSheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) : Prop :=
  Presheaf.IsSheaf J Q ∧
    ∀ (R : Cᵒᵖ ⥤ Type w), Presheaf.IsSheaf J R →
      ∀ f : P ⟶ R, ∃! g : Q ⟶ R, η ≫ g = f

def IsInducedMorphismPresheafMap {C : Type u} [Category.{v} C]
    {F G : FiberedCategory C} (η : FiberedMorphism F G) {U : C}
    (x y : Fiber F U)
    (φ : F.presheafHom x y ⟶
      G.presheafHom ((η.app (.mk (op U))).toFunctor.obj x)
        ((η.app (.mk (op U))).toFunctor.obj y)) : Prop :=
  ∀ (T : (Over C U)ᵒᵖ)
    (f : (F.map T.unop.hom.op.toLoc).toFunctor.obj x ⟶
      (F.map T.unop.hom.op.toLoc).toFunctor.obj y),
    (φ.app T) f =
      (η.naturality T.unop.hom.op.toLoc).inv.toNatTrans.app x ≫
        (η.app (.mk (op T.unop.left))).toFunctor.map f ≫
          (η.naturality T.unop.hom.op.toLoc).hom.toNatTrans.app y

structure Stackification (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStack : Stack value J
  locallyFromMap : ∀ (U : C) (x' : Fiber value U),
    ∃ (ι : Type t) (X : ι → C) (f : ∀ i, X i ⟶ U),
      CoveringFamily J f ∧
        ∀ i, ∃ x : Fiber F (X i), Nonempty
          ((value.map (f i).op.toLoc).toFunctor.obj x' ≅
            (map.app (.mk (op (X i)))).toFunctor.obj x)
  morphismPresheafMap : ∀ (U : C) (x y : Fiber F U),
    F.presheafHom x y ⟶
      value.presheafHom ((map.app (.mk (op U))).toFunctor.obj x)
        ((map.app (.mk (op U))).toFunctor.obj y)
  morphismPresheafMap_is_induced : ∀ (U : C) (x y : Fiber F U),
    IsInducedMorphismPresheafMap map x y (morphismPresheafMap U x y)
  morphismSheafification : ∀ (U : C) (x y : Fiber F U),
    IsSheafification (J.over U) (morphismPresheafMap U x y)

/- TODO(stacks-foundation): Treat `Stackification` as a foundational
construction, not as data to synthesize independently in every theorem.  The
proof order is: sheafify each morphism presheaf, construct objects by effective
descent, assemble reindexing/coherence, and finally prove the hom-category
universal property.  Groupoid stackification, inertia comparisons, and
pullback/localization results should only be attempted after that API exists. -/

structure RelativeInertiaObject {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object
  fixed : (η.app (.mk (op U))).toFunctor.map automorphism.hom = 𝟙 _

structure AbsoluteInertiaObject (F : FiberedCategory C) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object

end Formalization.Books.Stacks.Unit01
