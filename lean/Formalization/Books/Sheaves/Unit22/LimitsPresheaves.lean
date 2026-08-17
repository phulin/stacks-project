import Formalization.Books.Sheaves.Unit22.Skyscraper
import Mathlib.Topology.Sheaves.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Sheaves on Spaces, Chapter 22, Section 7: Limits and colimits of presheaves

Presheaf limits and colimits are Mathlib's pointwise limits and colimits in a
functor category.  The displayed section and stalk comparisons are exposed
with the canonical evaluation isomorphisms and source-facing theorem names.
-/

namespace Formalization.Books.Sheaves.Unit22

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe v

noncomputable section

/-! ## Pointwise limits and colimits -/

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

/-- Stalks preserve finite limits of set-valued presheaves. -/
theorem presheafStalkPreservesFiniteLimits {X : TopCat.{v}} (x : X) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  dsimp [TopCat.Presheaf.stalkFunctor]
  infer_instance

/-- Stalks do not preserve arbitrary limits in general. -/
theorem presheafStalkDoesNotPreserveAllLimits :
    ∃ (X : TopCat.{v}) (x : X),
      ¬ PreservesLimits (TopCat.Presheaf.stalkFunctor (Type v) x) := by
  sorry

/-- The finite-diagram stalk/limit comparison. -/
noncomputable def presheafFiniteLimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J] [Finite J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafLimit F).stalk x ≅
      limit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) := by
  letI := presheafStalkPreservesFiniteLimits x
  exact preservesLimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

/-- Stalks commute with arbitrary presheaf colimits. -/
noncomputable def presheafColimitStalkIso {X : TopCat.{v}} {J : Type v}
    [Category.{v} J]
    (F : J ⥤ TopCat.Presheaf (Type v) X) (x : X) :
    (presheafColimit F).stalk x ≅
      colimit (F ⋙ TopCat.Presheaf.stalkFunctor (Type v) x) := by
  exact preservesColimitIso (TopCat.Presheaf.stalkFunctor (Type v) x) F

end

end Formalization.Books.Sheaves.Unit22
