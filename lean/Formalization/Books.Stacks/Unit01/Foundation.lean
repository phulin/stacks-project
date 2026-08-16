import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Stacks, Chapter 1: shared interfaces

Mathlib's descent library presents a fibred category by a pseudofunctor to
`Cat`.  The chapter files use that established presentation directly.
-/

namespace Formalization.«Books.Stacks».Unit01

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
        refine ⟨⟨(F.presheafHom x y).map q g, ?_, ?_⟩⟩
        · rw [← (F.presheafHom x y).map_comp, h₁,
            (F.presheafHom x y).map_id]
        · rw [← (F.presheafHom x y).map_comp, h₂,
            (F.presheafHom x y).map_id]⟩ :
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

structure Substack (F : FiberedCategory C) (J : GrothendieckTopology C) where
  carrier : ∀ U : C, Set (Fiber F U)
  stableUnderPullback : Prop
  full : Prop
  locallyEssentiallyInCarrier : Prop

structure TwoFiberProductCone (F G H : FiberedCategory C) where
  apex : FiberedCategory C
  left : FiberedMorphism apex F
  right : FiberedMorphism apex G
  comparison : Prop

structure Stackification (F : FiberedCategory C) (J : GrothendieckTopology C) where
  value : FiberedCategory C
  map : FiberedMorphism F value
  isStack : Stack value J
  locallyFromMap : Prop
  morphismSheafification : Prop

structure SiteMorphismData (C D : Type*) [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) where
  functor : C ⥤ D
  continuous : Prop

structure RelativeInertiaObject {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (U : C) where
  object : Fiber F U
  automorphism : object ⟶ object
  fixed : (η.app (.mk (op U))).toFunctor.map automorphism = 𝟙 _

def AbsoluteInertiaObject (F : FiberedCategory C) (U : C) :=
  RelativeInertiaObject (η := (𝟙 F : F ⟶ F)) U

end Formalization.«Books.Stacks».Unit01
