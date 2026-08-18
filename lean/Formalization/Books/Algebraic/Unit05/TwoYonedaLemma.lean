import Formalization.Books.Categories.Unit41.TwoYonedaLemma
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over

/-!
# Algebraic Stacks, Chapter 5: The 2-Yoneda lemma

The relative fppf site of schemes over a fixed scheme has the same underlying
category as `CategoryTheory.Over`; the topology is recorded separately.  The
2-Yoneda constructions themselves use only this underlying category, so the
canonical fibre, pullback-choice, and 2-Yoneda interfaces from the Categories
chapters apply directly.
-/

namespace Formalization.Books.Algebraic.Unit05

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Functor
open Formalization.Books.Categories.Unit33
open Formalization.Books.Categories.Unit41

universe u v w

noncomputable section

/-! ## The relative fppf site -/

/-- The underlying category of the big fppf site of schemes over `S`. -/
abbrev RelativeSite (S : Scheme.{u}) := CategoryTheory.Over S

/-- The fppf topology on the relative site of schemes over `S`. -/
abbrev RelativeFppfTopology (S : Scheme.{u}) :
    GrothendieckTopology (RelativeSite S) :=
  Scheme.fppfTopology.over S

/-! ## Evaluation at `U/U` -/

/- A category fibred in groupoids over the relative site is represented by a
   projection functor.  The source's category of morphisms over the base is
   Mathlib's fibre of postcomposition, specialized to `Over U`. -/
abbrev RelativeTwoYonedaMorphismCategory
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) (U : RelativeSite S) :=
  twoYonedaGroupoidMorphismCategory p U

/-- The fibre of a relative fibred category over a scheme `U/S`. -/
abbrev RelativeFibre
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) (U : RelativeSite S) :=
  Functor.Fiber p U

/-- Evaluation of a relative morphism at the identity object `U/U`. -/
abbrev RelativeTwoYonedaEvaluation
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) (U : RelativeSite S) :
    RelativeTwoYonedaMorphismCategory p U ⥤ RelativeFibre p U :=
  twoYonedaEvaluationCore p U

/-- The underlying object of evaluation is the value at `U/U`. -/
theorem relativeTwoYonedaEvaluation_obj_formula
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) (U : RelativeSite S)
    (G : RelativeTwoYonedaMorphismCategory p U) :
    ((RelativeTwoYonedaEvaluation p U).obj G).1 =
      G.1.obj (Over.mk (𝟙 U)) := by
  rfl

/-- The value at `U/U` lies in the fibre over `U`. -/
theorem relativeTwoYonedaEvaluation_obj_isFiber
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) (U : RelativeSite S)
    (G : RelativeTwoYonedaMorphismCategory p U) :
    p.obj (G.1.obj (Over.mk (𝟙 U))) = U := by
  exact twoYonedaEvaluationCore_obj_isFiber p U G

/-- The morphism category of relative 2-Yoneda is a groupoid. -/
theorem relativeTwoYonedaMorphismCategory_isGroupoid
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (U : RelativeSite S) :
    IsGroupoid (RelativeTwoYonedaMorphismCategory p U) := by
  exact twoYonedaGroupoidMorphismCategory_isGroupoid p U

/-- The relative 2-Yoneda equivalence, evaluated at `U/U`. -/
theorem relative_two_yoneda_equivalence
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (U : RelativeSite S) :
    (RelativeTwoYonedaEvaluation p U).IsEquivalence := by
  exact twoYoneda_groupoid_equivalence p U

/-! ## The functor associated to an object of the fibre -/

/- The chosen-pullback construction is the source's functor
`(V → U) ↦ V^* x`.  Its morphism component and the proof that it is over the
base are supplied by the Categories 2-Yoneda interface. -/
abbrev RelativeTwoYonedaFromFibre
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (U : RelativeSite S) :
    RelativeFibre p U ⥤ RelativeTwoYonedaMorphismCategory p U :=
  twoYonedaGroupoidPullback p P U

/-- The object formula of the functor associated to `x : X_U`. -/
theorem relativeTwoYonedaFromFibre_obj_formula
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (U : RelativeSite S)
    (x : RelativeFibre p U) (f : Over U) :
    ((RelativeTwoYonedaFromFibre p P U).obj x).1.obj f =
      Functor.Fiber.fiberInclusion.obj (P.pullback f.hom x) := by
  rfl

/-- The functor associated to `x` is strictly over the relative base. -/
theorem relativeTwoYonedaFromFibre_isOver
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (U : RelativeSite S)
    (x : RelativeFibre p U) :
    ((RelativeTwoYonedaFromFibre p P U).obj x).1 ⋙ p =
      Over.forget U := by
  exact ((RelativeTwoYonedaFromFibre p P U).obj x).2

/- The source states the value at `U/U` as an equality.  The project-wide
   pullback-choice API supplies this equality for a unital choice and supplies
   an isomorphism for an arbitrary choice. -/
theorem relativeTwoYonedaFromFibre_evaluation_iso
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (U : RelativeSite S)
    (x : RelativeFibre p U) :
    Nonempty
      ((RelativeTwoYonedaEvaluation p U).obj
          ((RelativeTwoYonedaFromFibre p P U).obj x) ≅ x) := by
  exact ⟨asIso (Classical.choose (pullback_identity_iso p P U)).inv.app x⟩

/-- With the standard unital normalization of pullbacks, evaluation recovers
`x` literally at `U/U`. -/
theorem relativeTwoYonedaFromFibre_evaluation
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (hP : P.IsUnital) (U : RelativeSite S)
    (x : RelativeFibre p U) :
    (RelativeTwoYonedaEvaluation p U).obj
        ((RelativeTwoYonedaFromFibre p P U).obj x) = x := by
  change P.pullback (𝟙 U) x = x
  exact hP U x

/- The unnormalized wording "a unique 2-isomorphism" is made precise by
   prescribing its value under evaluation.  This is the usual uniqueness
   statement supplied by the fully faithful part of the equivalence. -/
theorem relativeTwoYoneda_existsUnique_normalizedIso
    {S : Scheme.{u}} {E : Type v} [Category.{w} E]
    (p : E ⥤ RelativeSite S) [p.IsFibredInGroupoids]
    (P : PullbackChoice p) (U : RelativeSite S)
    (x : RelativeFibre p U)
    (G : RelativeTwoYonedaMorphismCategory p U)
    (hG : (RelativeTwoYonedaEvaluation p U).obj G = x)
    (a : (RelativeTwoYonedaEvaluation p U).obj
        ((RelativeTwoYonedaFromFibre p P U).obj x) ≅ x) :
    ∃! η : (RelativeTwoYonedaFromFibre p P U).obj x ⟶ G,
        IsIso η ∧
        (RelativeTwoYonedaEvaluation p U).map η =
          a.hom ≫ eqToHom hG.symm := by
  letI : (RelativeTwoYonedaEvaluation p U).IsEquivalence :=
    relative_two_yoneda_equivalence p U
  let η : (RelativeTwoYonedaFromFibre p P U).obj x ⟶ G :=
    (RelativeTwoYonedaEvaluation p U).preimage
      (a.hom ≫ eqToHom hG.symm)
  have hη : (RelativeTwoYonedaEvaluation p U).map η =
      a.hom ≫ eqToHom hG.symm :=
    (RelativeTwoYonedaEvaluation p U).map_preimage _
  refine ⟨η, ?_, ?_⟩
  · constructor
    · haveI : IsIso ((RelativeTwoYonedaEvaluation p U).map η) := by
        rw [hη]
        infer_instance
      exact (Functor.FullyFaithful.ofFullyFaithful
        (RelativeTwoYonedaEvaluation p U)).isIso_of_isIso_map η
    · exact hη
  · intro η' hη'
    apply (Functor.FullyFaithful.ofFullyFaithful
      (RelativeTwoYonedaEvaluation p U)).map_injective
    exact hη'.2.trans hη.symm

end

end Formalization.Books.Algebraic.Unit05
