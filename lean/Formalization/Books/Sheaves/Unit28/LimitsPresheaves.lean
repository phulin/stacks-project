import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Sheaves on Spaces, Chapter 28: Limits and colimits of presheaves

Set-valued presheaves are functors on the opposite category of opens.  Their
limits and colimits are therefore the canonical functor-category limits and
colimits, and evaluation gives the sectionwise comparison isomorphisms.  The
stalk assertions are recorded with the corresponding categorical preservation
interfaces and comparison isomorphisms.
-/

namespace Formalization.Books.Sheaves.Unit28

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

/-! ## Pointwise limits and colimits -/

/- The source's existence assertion is the completeness and cocompleteness of
   the functor category of set-valued presheaves. -/

/-- The category of set-valued presheaves has all limits. -/
theorem presheaf_has_limits {X : TopCat.{v}} :
    HasLimits (TopCat.Presheaf (Type v) X) := by
  infer_instance

/-- The category of set-valued presheaves has all colimits. -/
theorem presheaf_has_colimits {X : TopCat.{v}} :
    HasColimitsOfSize.{v, v} (TopCat.Presheaf (Type v) X) := by
  infer_instance

/-- The limit of a diagram of set-valued presheaves. -/
noncomputable abbrev presheafLimit {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf (Type v) X :=
  limit F

/-- The colimit of a diagram of set-valued presheaves. -/
noncomputable abbrev presheafColimit {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) :
    TopCat.Presheaf (Type v) X :=
  colimit F

/- The displayed section formulas are the pointwise functor-category
   comparison isomorphisms. -/

/-- The pointwise limit formula on sections over an open. -/
noncomputable def presheafLimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) (U : Opens X) :
    (presheafLimit F).obj (op U) ≅
      limit (F ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  limitObjIsoLimitCompEvaluation F (op U)

/-- The pointwise colimit formula on sections over an open. -/
noncomputable def presheafColimitSectionsIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] (F : J ⥤ TopCat.Presheaf (Type v) X) (U : Opens X) :
    (presheafColimit F).obj (op U) ≅
      colimit (F ⋙ (evaluation (Opens X)ᵒᵖ (Type v)).obj (op U)) :=
  colimitObjIsoColimitCompEvaluation F (op U)

/-! ## Stalks -/

/- The source's left-exactness assertion is exposed as preservation of finite
   limits.  The proof that the stalk colimit has this property is deferred to
   the proof stage. -/

/-- Stalks preserve finite limits of set-valued presheaves. -/
theorem presheafStalkPreservesFiniteLimits {X : TopCat.{v}} (x : X) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  sorry

/-- Stalks do not preserve arbitrary limits in general. -/
theorem presheafStalkDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}) (x : X),
      ¬ PreservesLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  sorry

/-- The finite-diagram stalk/limit comparison. -/
noncomputable def presheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [FinCategory J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafLimit F).stalk x ≅
      limit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) := by
  letI := presheafStalkPreservesFiniteLimits x
  exact preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

/- The source's arbitrary-colimit stalk equality is represented by its
   canonical comparison isomorphism. -/

/-- Stalks commute with arbitrary presheaf colimits. -/
theorem exists_presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    Nonempty ((presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x)) := by
  sorry

/-- A chosen stalk/colimit comparison isomorphism. -/
noncomputable def presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) :=
  Classical.choice (exists_presheafColimitStalkIso F x)

end

end Formalization.Books.Sheaves.Unit28
