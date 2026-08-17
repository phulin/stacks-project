import Formalization.Books.Categories.Unit03.Opposite
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
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

/- The preceding observation is made explicit using representations of the
   two presheaves and an object-level pullback square. -/
theorem presheafPullback_representation_of_isPullback
    {F G : Presheaf C} (a : F ⟶ G)
    {X Y U P : C}
    (sF : representablePresheaf X ≅ F)
    (sG : representablePresheaf Y ≅ G)
    (f : X ⟶ Y) (g : U ⟶ Y) (ξ : G.obj (op U))
    (ha : (functorOfPoints (C := C)).map f ≫ sG.hom = sF.hom ≫ a)
    (hξ : sG.hom.app (op U) g = ξ)
    {p : P ⟶ X} {q : P ⟶ U}
    (h : IsPullback p q f g) :
    Nonempty
      (representablePresheaf P ≅
        pullback ((yonedaBijection U G).symm ξ) a) := by
  sorry

/-! ## The Yoneda special case -/

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
    ((yonedaBijection U G).symm ξ).app (op X) f = a.app (op X) ξ' ↔
      G.map f.op ξ = a.app (op X) ξ' := by
  rw [yonedaBijection_inverse_app_apply ξ f]

/-- The pointwise pullback in the Yoneda special case is equivalent to the
explicit fibre displayed in the source. -/
noncomputable def yonedaPullbackObjEquiv
    {F G : Presheaf C} (a : F ⟶ G) (U : C) (ξ : G.obj (op U)) (X : C) :
    (pullback ((yonedaBijection U G).symm ξ) a).obj (op X) ≃
      yonedaPullbackFiber a U ξ X :=
  (presheafPullbackObjIso ((yonedaBijection U G).symm ξ) a X).toEquiv.trans
    (Equiv.subtypeEquiv (Equiv.refl _) fun p =>
      yoneda_pullback_condition_iff a ξ p.1 p.2)

/-! ## Representable morphisms of presheaves -/

/- The source's relative representability condition is Mathlib's canonical
   `yoneda.relativelyRepresentable` property.  It quantifies over maps from
   representables and records a represented pullback square directly, which is
   equivalent to saying that the chosen presheaf pullback is representable. -/

/-- If a representable presheaf morphism has representable target, then its
source is representable. -/
theorem isRepresentable_of_representablePresheafMorphism
    {F G : Presheaf C} (a : F ⟶ G)
    (ha : yoneda.relativelyRepresentable a)
    (hG : Functor.IsRepresentable G) :
    Functor.IsRepresentable F := by
  sorry

/-! ## The diagonal criterion -/

/-- The three equivalent criteria for a presheaf to have representable
diagonal, under the source's product and fibre-product hypotheses. -/
theorem representable_diagonal_iff
    {F : Presheaf C} [HasBinaryProducts C] [HasPullbacks C] :
    (yoneda.relativelyRepresentable (Limits.diag F) ↔
      (∀ (U : C) (ξ : F.obj (op U)),
        yoneda.relativelyRepresentable ((yonedaBijection U F).symm ξ))) ∧
    ((∀ (U : C) (ξ : F.obj (op U)),
        yoneda.relativelyRepresentable ((yonedaBijection U F).symm ξ)) ↔
      (∀ (U V : C) (ξ : F.obj (op U)) (ξ' : F.obj (op V)),
        Functor.IsRepresentable
          (pullback ((yonedaBijection U F).symm ξ)
            ((yonedaBijection V F).symm ξ')))) := by
  sorry

end Formalization.Books.Categories.Unit08
