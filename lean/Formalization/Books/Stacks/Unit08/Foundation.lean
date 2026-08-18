import Formalization.Books.Stacks.Unit07.Inertia
import Formalization.Books.Stacks.Unit04.Foundation

/-!
# Stacks, Unit 8: stackification interfaces

These declarations retain their established namespace for downstream compatibility,
but are owned by the source unit corresponding to this file path.
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

def IsSheafification {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C)
    {P Q : Cᵒᵖ ⥤ Type w} (η : P ⟶ Q) : Prop :=
  Presheaf.IsSheaf J Q ∧
    ∀ (R : Cᵒᵖ ⥤ Type w), Presheaf.IsSheaf J R →
      ∀ f : P ⟶ R, ∃! g : Q ⟶ R, η ≫ g = f


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

end Formalization.Books.Stacks.Unit01

