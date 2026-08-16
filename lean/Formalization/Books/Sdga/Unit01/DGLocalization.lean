import Formalization.Books.Sdga.Unit01.Core

/-! # 19. Localization and sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure DGLocalizationData {S T : RingedSite.{u,v} R}
    (A : DGAlgebra S) (B : DGAlgebra T) where
  localization_map : RingedSiteMorphism T S
  extension_by_zero : DGModule T B → DGModule S A
  restriction : DGModule S A → DGModule T B
  extension_adjunction : Prop
  exact_extension : Prop
  tensor_compatibility : Prop

def extensionByZeroDG {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) := j.extension_by_zero

def restrictionDG {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) := j.restriction

def dgExtensionByZeroExact {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) : Prop := j.exact_extension

def dgExtensionByZeroTensorCompatibility {S T : RingedSite.{u,v} R}
    {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) : Prop := j.tensor_compatibility

theorem lemma_extension_by_zero_dg
    {S T : RingedSite.{u,v} R} {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) : j.extension_adjunction ∧ j.exact_extension := by
  sorry

theorem lemma_tensor_with_extension_by_zero_dg
    {S T : RingedSite.{u,v} R} {A : DGAlgebra S} {B : DGAlgebra T}
    (j : DGLocalizationData A B) : j.tensor_compatibility := by
  sorry

end Sdga
