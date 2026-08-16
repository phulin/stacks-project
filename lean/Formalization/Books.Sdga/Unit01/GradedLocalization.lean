import Formalization.«Books.Sdga».Unit01.Core

/-! # 10. Localization and sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure GradedLocalizationData {S T : RingedSite.{u,v} R}
    (A : GradedAlgebra S) (B : GradedAlgebra T) where
  localization_map : RingedSiteMorphism T S
  extension_by_zero : GradedModule T B → GradedModule S A
  restriction : GradedModule S A → GradedModule T B
  extension_adjunction : Prop
  exact_extension : Prop
  tensor_compatibility : Prop

def extensionByZeroGraded {S T : RingedSite.{u,v} R}
    {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) := j.extension_by_zero

theorem lemma_extension_by_zero_graded
    {S T : RingedSite.{u,v} R} {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) : j.extension_adjunction ∧ j.exact_extension := by
  sorry

theorem lemma_tensor_with_extension_by_zero
    {S T : RingedSite.{u,v} R} {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) : j.tensor_compatibility := by
  exact j.tensor_compatibility

end Sdga
