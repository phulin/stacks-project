import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.Tactic.CategoryTheory.Bicategory.PureCoherence
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.IsomorphismClasses
import Formalization.Books.Categories.Unit31.TwoFibreProducts

/-!
# Stacks, Chapter 1: shared interfaces

Mathlib's descent library presents a fibred category by a pseudofunctor to
`Cat`.  The chapter files use that established presentation directly.
-/

namespace Formalization.Books.Stacks.Unit01

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open Formalization.Books.Categories.Unit31
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
  map {T₁ T₂} q := ↾fun f => ⟨(F.presheafHom x y).map q f.1, by
    let _ := f.property
    dsimp [Pseudofunctor.presheafHom,
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    infer_instance⟩
  map_id T := by
    ext f
    simp
  map_comp f g := by
    ext h
    simp

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


/-! ### Object-isomorphism classes used by the Section 2 presentation -/

abbrev ObjectIsoSetoid (K : Type u) [Category.{v} K] : Setoid K :=
  CategoryTheory.isIsomorphicSetoid K

def ObjectIsomorphismClasses {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (U : C) :=
  Quotient (ObjectIsoSetoid (Fiber F U))

def ObjectClassPresheaf {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) : Cᵒᵖ ⥤ Type w where
  obj U := ObjectIsomorphismClasses F U.unop
  map {U V} f := ↾(Quotient.map
    (fun x => (F.map f.toLoc).toFunctor.obj x)
    (by
      intro x y h
      rcases h with ⟨e⟩
      exact ⟨(F.map f.toLoc).toFunctor.mapIso e⟩))
  map_id := by
    intro U
    ext z
    refine Quotient.inductionOn z ?_
    intro x
    apply Quotient.sound
    exact ⟨(Cat.Hom.toNatIso (F.mapId (.mk U))).app x⟩
  map_comp := by
    intro U V W f g
    ext z
    refine Quotient.inductionOn z ?_
    intro x
    apply Quotient.sound
    exact ⟨(Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).app x⟩

theorem object_class_presheaf_fibre {C : Type u} [Category.{v} C]
    (F : FiberedCategory C) (U : C) :
    (ObjectClassPresheaf F).obj (op U) = ObjectIsomorphismClasses F U := rfl

/-! ### The map on morphism presheaves induced by a fibred morphism -/

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


end Formalization.Books.Stacks.Unit01
