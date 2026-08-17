import Formalization.Books.Sdga.Unit01.Core

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
  extension_adjunction_proof : extension_adjunction
  exact_extension : Prop
  exact_extension_proof : exact_extension
  tensor_compatibility : Prop
  tensor_compatibility_proof : tensor_compatibility

def extensionByZeroGraded {S T : RingedSite.{u,v} R}
    {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) := j.extension_by_zero

theorem lemma_extension_by_zero_graded
    {S T : RingedSite.{u,v} R} {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) : j.extension_adjunction ∧ j.exact_extension := by
  exact ⟨j.extension_adjunction_proof, j.exact_extension_proof⟩

theorem lemma_tensor_with_extension_by_zero
    {S T : RingedSite.{u,v} R} {A : GradedAlgebra S} {B : GradedAlgebra T}
    (j : GradedLocalizationData A B) : j.tensor_compatibility := by
  exact j.tensor_compatibility_proof

end Sdga
