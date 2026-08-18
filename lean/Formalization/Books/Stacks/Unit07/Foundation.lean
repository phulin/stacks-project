import Formalization.Books.Stacks.Unit06.Setoids

/-!
# Stacks, Unit 7: inertia object interfaces

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

structure RelativeInertiaObject {F G : FiberedCategory C}
    (η : FiberedMorphism F G) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object
  fixed : (η.app (.mk (op U))).toFunctor.map automorphism.hom = 𝟙 _

structure AbsoluteInertiaObject (F : FiberedCategory C) (U : C) where
  object : Fiber F U
  automorphism : object ≅ object


end Formalization.Books.Stacks.Unit01

