import Formalization.Books.Categories.Unit04.Products
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Categories, Chapter 8: Fibre products and representability

The source's presheaf fibre products are Mathlib's pullbacks in a functor
category.  The pointwise description is recorded by the canonical evaluation
isomorphism, and the set-theoretic fibre appearing in the source is recorded
using `Types.PullbackObj` and the Yoneda formula from Chapter 3.
-/

namespace Formalization.Books.Categories.Unit08

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Categories.Unit03
open Opposite

universe v u

variable {C : Type u} [Category.{v} C]

/-! ## Fibre products of presheaves -/

/-- Pullbacks of morphisms of presheaves exist because pullbacks of types exist
and functor-category limits are computed pointwise. -/
theorem hasPullback_presheaves
    {F G H : Presheaf C} (a : F ⟶ G) (b : H ⟶ G) :
    HasPullback a b := by
  infer_instance

/-- The source's pointwise formula for a pullback of presheaves.

Mathlib chooses a pullback object in `Type v`; this is canonically isomorphic
to the explicit subtype of pairs satisfying the fibre equation. -/
noncomputable def presheafPullbackObjIso
    {F G H : Presheaf C} (a : F ⟶ G) (b : H ⟶ G) (X : C) :
    (pullback a b).obj (op X) ≅
      Types.PullbackObj (a.app (op X)) (b.app (op X)) :=
  pullbackObjIso a b (op X) ≪≫
    Types.pullbackIsoPullback (a.app (op X)) (b.app (op X))

/-!
The sentence following the source's special-case formula says that, when the
other presheaves are representable, this pointwise pullback is the presheaf
representing the corresponding fibre product whenever that object exists.
The Yoneda equivalence together with `presheafPullbackObjIso` is the canonical
interface for that observation, so it does not require a second parallel
definition of a presheaf fibre product.
-/

/-! ## The Yoneda special case -/

/-- The natural transformation induced by an element of a presheaf, as in the
source's notation `ξ : h_U ⟶ G`. -/
def yonedaElementMap
    {G : Presheaf C} (U : C) (ξ : G.obj (op U)) :
    representablePresheaf U ⟶ G :=
  (yonedaBijection U G).symm ξ

/-- The explicit set occurring in the source's description of
`h_U ×_{ξ,G,a} F` at an object `X`. -/
def yonedaPullbackFiber
    {F G : Presheaf C} (a : F ⟶ G) (U : C) (ξ : G.obj (op U)) (X : C) : Type v :=
  {p : (X ⟶ U) × F.obj (op X) //
    G.map p.1.op ξ = a.app (op X) p.2}

/-- The Yoneda formula rewrites the pullback condition as the source's
`G(f)(ξ) = a_X(ξ')`. -/
theorem yoneda_pullback_condition_iff
    {F G : Presheaf C} (a : F ⟶ G) {U X : C}
    (ξ : G.obj (op U)) (f : X ⟶ U) (ξ' : F.obj (op X)) :
    (yonedaElementMap U ξ).app (op X) f = a.app (op X) ξ' ↔
      G.map f.op ξ = a.app (op X) ξ' := by
  change (((yonedaBijection U G).symm ξ).app (op X)) f =
      a.app (op X) ξ' ↔ G.map f.op ξ = a.app (op X) ξ'
  rw [yonedaBijection_inverse_app_apply ξ f]

/-- The pointwise pullback in the Yoneda special case is equivalent to the
explicit fibre displayed in the source. -/
noncomputable def yonedaPullbackObjEquiv
    {F G : Presheaf C} (a : F ⟶ G) (U : C) (ξ : G.obj (op U)) (X : C) :
    (pullback (yonedaElementMap U ξ) a).obj (op X) ≃
      yonedaPullbackFiber a U ξ X :=
  (presheafPullbackObjIso (yonedaElementMap U ξ) a X).toEquiv.trans
    (Equiv.subtypeEquiv (Equiv.refl _) fun p =>
      yoneda_pullback_condition_iff a ξ p.1 p.2)

/-! ## Representable morphisms of presheaves -/

/-- A morphism of presheaves is representable when every pullback along a
map from a representable presheaf is representable. -/
def RepresentablePresheafMorphism
    {F G : Presheaf C} (a : F ⟶ G) : Prop :=
  ∀ (U : C) (ξ : G.obj (op U)),
    Functor.IsRepresentable (pullback (yonedaElementMap U ξ) a)

/-- If a representable presheaf morphism has representable target, then its
source is representable. -/
theorem isRepresentable_of_representablePresheafMorphism
    {F G : Presheaf C} (a : F ⟶ G)
    (ha : RepresentablePresheafMorphism a)
    (hG : Functor.IsRepresentable G) :
    Functor.IsRepresentable F := by
  sorry

/-! ## The diagonal criterion -/

/-- The diagonal natural transformation into the explicit pointwise product
of a presheaf with itself. -/
def presheafDiagonal (F : Presheaf C) :
    F ⟶ FunctorToTypes.prod F F :=
  FunctorToTypes.prod.lift (𝟙 F) (𝟙 F)

/-- The three equivalent criteria for a presheaf to have representable
diagonal, under the source's product and fibre-product hypotheses. -/
theorem representable_diagonal_iff
    {F : Presheaf C} [HasBinaryProducts C] [HasPullbacks C] :
    (RepresentablePresheafMorphism (presheafDiagonal F) ↔
      (∀ (U : C) (ξ : F.obj (op U)),
        RepresentablePresheafMorphism (yonedaElementMap U ξ))) ∧
    ((∀ (U : C) (ξ : F.obj (op U)),
        RepresentablePresheafMorphism (yonedaElementMap U ξ)) ↔
      (∀ (U V : C) (ξ : F.obj (op U)) (ξ' : F.obj (op V)),
        Functor.IsRepresentable
          (pullback (yonedaElementMap U ξ) (yonedaElementMap V ξ')))) := by
  sorry

end Formalization.Books.Categories.Unit08
