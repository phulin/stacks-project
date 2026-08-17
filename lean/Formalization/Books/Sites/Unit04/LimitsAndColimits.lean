import Formalization.Books.Sites.Unit02.Presheaves
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Sites and Sheaves, Chapter 4: Limits and colimits of presheaves

This file formalizes the precise assertions in `books/sites.tex`, lines
295--366.  Mathlib's functor-category limits and colimits are the canonical
pointwise constructions, and its evaluation functors preserve them.  The
declarations below expose those interfaces in the source's presheaf
terminology.

The source does not discuss universes.  Here a diagram indexed by `I` is
assumed to be `v`-small, where `v` is the universe of the values of a
set-valued presheaf.  This is exactly the size condition under which the
category `Type v` has the required limits and colimits.
-/

namespace Formalization.Books.Sites.Unit04

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Sites.Unit02
open Opposite

universe u v w w'

variable {C : Type u} [Category.{v} C]
variable {I : Type w} [Category.{w'} I] [Small.{v} I]

/-! ## Diagrams and existence -/

/-- A diagram of set-valued presheaves on `C`. -/
abbrev PresheafDiagram (C : Type u) [Category.{v} C]
    (I : Type w) [Category.{w'} I] := I ⥤ Presheaf C

/-- Small diagrams of presheaves have limits. -/
theorem presheaf_has_limits_of_shape :
    HasLimitsOfShape I (Presheaf C) := by
  infer_instance

/-- Small diagrams of presheaves have colimits. -/
theorem presheaf_has_colimits_of_shape :
    HasColimitsOfShape I (Presheaf C) := by
  infer_instance

/-! ## Pointwise evaluation -/

/-- Evaluation at an object of `C` preserves `I`-shaped limits of presheaves. -/
theorem evaluation_preserves_presheaf_limits (U : C) :
    PreservesLimitsOfShape I
      ((evaluation (Cᵒᵖ) (Type v)).obj (op U)) := by
  infer_instance

/-- Evaluation at an object of `C` preserves `I`-shaped colimits of presheaves. -/
theorem evaluation_preserves_presheaf_colimits (U : C) :
    PreservesColimitsOfShape I
      ((evaluation (Cᵒᵖ) (Type v)).obj (op U)) := by
  infer_instance

/-! ## The pointwise limit presheaf -/

/-- The pointwise limit presheaf, using Mathlib's canonical functor-category
limit. -/
noncomputable def pointwiseLimitPresheaf
    (F : PresheafDiagram C I) : Presheaf C :=
  limit F

/-- The canonical limiting cone on a diagram of presheaves. -/
noncomputable def pointwiseLimitCone
    (F : PresheafDiagram C I) : Cone F :=
  limit.cone F

/-- The canonical projection from the pointwise limit presheaf. -/
noncomputable def pointwiseLimitProjection
    (F : PresheafDiagram C I) (i : I) :
    pointwiseLimitPresheaf F ⟶ F.obj i :=
  limit.π F i

/-- The canonical pointwise limit cone is limiting. -/
noncomputable def pointwiseLimitConeIsLimit
    (F : PresheafDiagram C I) : IsLimit (pointwiseLimitCone F) :=
  limit.isLimit F

/-- Evaluation identifies the limit presheaf's sections with the limit of
the corresponding diagram of sets. -/
noncomputable def pointwiseLimitEvaluationIso
    (F : PresheafDiagram C I) (U : C) :
    (pointwiseLimitPresheaf F).obj (op U) ≅
      limit (F ⋙ (evaluation (Cᵒᵖ) (Type v)).obj (op U)) :=
  limitObjIsoLimitCompEvaluation F (op U)

/-- The universal map from any cone into the pointwise limit presheaf is
unique with respect to all projections. -/
theorem pointwiseLimit_universal
    (F : PresheafDiagram C I) (s : Cone F) :
    ∃! q : s.pt ⟶ pointwiseLimitPresheaf F,
      ∀ i, q ≫ pointwiseLimitProjection F i = s.π.app i := by
  exact (pointwiseLimitConeIsLimit F).existsUnique s

/-! ## The pointwise colimit presheaf -/

/-- The pointwise colimit presheaf, using Mathlib's canonical functor-category
colimit. -/
noncomputable def pointwiseColimitPresheaf
    (F : PresheafDiagram C I) : Presheaf C :=
  colimit F

/-- The canonical colimiting cocone on a diagram of presheaves. -/
noncomputable def pointwiseColimitCocone
    (F : PresheafDiagram C I) : Cocone F :=
  colimit.cocone F

/-- The canonical injection into the pointwise colimit presheaf. -/
noncomputable def pointwiseColimitInjection
    (F : PresheafDiagram C I) (i : I) :
    F.obj i ⟶ pointwiseColimitPresheaf F :=
  colimit.ι F i

/-- The canonical pointwise colimit cocone is colimiting. -/
noncomputable def pointwiseColimitCoconeIsColimit
    (F : PresheafDiagram C I) :
    IsColimit (pointwiseColimitCocone F) :=
  colimit.isColimit F

/-- Evaluation identifies the colimit presheaf's sections with the colimit of
the corresponding diagram of sets. -/
noncomputable def pointwiseColimitEvaluationIso
    (F : PresheafDiagram C I) (U : C) :
    (pointwiseColimitPresheaf F).obj (op U) ≅
      colimit (F ⋙ (evaluation (Cᵒᵖ) (Type v)).obj (op U)) :=
  colimitObjIsoColimitCompEvaluation F (op U)

/-- The universal map from the pointwise colimit presheaf to any cocone point
is unique with respect to all injections. -/
theorem pointwiseColimit_universal
    (F : PresheafDiagram C I) (s : Cocone F) :
    ∃! q : pointwiseColimitPresheaf F ⟶ s.pt,
      ∀ i, pointwiseColimitInjection F i ≫ q = s.ι.app i := by
  exact (pointwiseColimitCoconeIsColimit F).existsUnique s

end Formalization.Books.Sites.Unit04
