import Formalization.Books.Sheaves.Unit22.RingedSpaces
import Formalization.Books.Sheaves.Unit04.AbelianPresheaves
import Formalization.Books.Sheaves.Unit15.AlgebraicStructures
import Formalization.Books.Sheaves.Unit16.ExactnessAndPoints
import Formalization.Books.Algebra.Unit12.TensorProducts

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Formalization.Books.Sheaves.Unit04
open Formalization.Books.Sheaves.Unit05
open Formalization.Books.Sheaves.Unit10
open Formalization.Books.Sheaves.Unit15
open Formalization.Books.Sheaves.Unit16

namespace Formalization.Books.Modules.Unit15

universe v

noncomputable section

#check HasLimit.isoOfNatIso
#check Discrete.compNatIsoDiscrete
#check Functor.mapIso
#check Functor.isoWhiskerLeft
#check NatIso.ofComponents
#check Formalization.Books.Sheaves.Unit07.Sh
#synth PreservesLimit (pair (TypeCat.of Bool) (TypeCat.of Bool))
  (TopCat.Presheaf.stalkFunctor (Type v) (default : Type v))

abbrev SetSheaf (X : TopCat.{v}) := TopCat.Sheaf (Type v) X

noncomputable def sheafProductSectionsEquiv {X : TopCat.{v}}
    (F G : SetSheaf X) (U : Opens X) :
    (((TopCat.Sheaf.forget (Type v) X).obj (limit (pair F G))).obj
      (op U) : Type v) ≃
      (F.presheaf.obj (op U) : Type v) ×
        (G.presheaf.obj (op U) : Type v) := by
  let e₁ := (preservesLimitIso (TopCat.Sheaf.forget (Type v) X)
    (pair F G)).app (op U)
  let e₁' := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair => (pair F G).obj (Discrete.mk j))
    (TopCat.Sheaf.forget (Type v) X))
  let e₂ := preservesLimitIso
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U))
    (Discrete.functor ((TopCat.Sheaf.forget (Type v) X).obj ∘ fun j : WalkingPair =>
      (pair F G).obj (Discrete.mk j)))
  let e₃ := HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete
    (fun j : WalkingPair =>
      (TopCat.Sheaf.forget (Type v) X).obj
        ((pair F G).obj (Discrete.mk j)))
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)))
  let e₄ := (Types.productIso (fun j : WalkingPair =>
    ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
      ((TopCat.Sheaf.forget (Type v) X).obj
        ((pair F G).obj (Discrete.mk j))))).toEquiv
  let e₅ : (∀ j : WalkingPair,
      ((evaluation ((Opens X)ᵒᵖ) (Type v)).obj (op U)).obj
        ((TopCat.Sheaf.forget (Type v) X).obj
          ((pair F G).obj (Discrete.mk j)))) ≃
      (F.presheaf.obj (op U) : Type v) ×
        (G.presheaf.obj (op U) : Type v) := {
    toFun := fun s => (s WalkingPair.left, s WalkingPair.right)
    invFun := fun p j => match j with
      | WalkingPair.left => p.1
      | WalkingPair.right => p.2
    left_inv := by
      intro s
      funext j
      cases j <;> rfl
    right_inv := by
      intro p
      rcases p with ⟨p, q⟩
      rfl }
  exact e₁.toEquiv.trans ((e₁'.app (op U)).toEquiv.trans
    (e₂.toEquiv.trans (e₃.toEquiv.trans (e₄.trans e₅))))

end

end Formalization.Books.Modules.Unit15
