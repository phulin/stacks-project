import Formalization.«Books.Sdga».Unit01.Core

/-! # 17. Sheaves of differential graded bimodules and tensor-hom adjunction -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGBimoduleSheaf {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) := DGBimodule S A B

structure DGTensorHomAdjunction {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) where
  tensor : DGModule S A → DGModule S B
  internal_hom : DGModule S B → DGModule S A
  hom_isomorphism : Prop
  internal_hom_isomorphism : Prop

structure DGRestrictionExtensionAdjunction {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) where
  extension : DGModule S A → DGModule S B
  restriction : DGModule S B → DGModule S A
  hom_isomorphism : Prop

theorem lemma_what_makes_a_bimodule_dg
    {S : RingedSite.{u,v} R} {A B : DGAlgebra S}
    (M : DGBimoduleSheaf A B) : M.leibniz ∧ M.differential_squared := by
  sorry

theorem lemma_tensor_hom_adjunction_dg
    {S : RingedSite.{u,v} R} (A B : DGAlgebra S)
    (F : DGTensorHomAdjunction A B) :
    F.hom_isomorphism ∧ F.internal_hom_isomorphism := by
  sorry

theorem lemma_adjunction_push_pull_dg
    {S : RingedSite.{u,v} R} (A B : DGAlgebra S)
    (F : DGRestrictionExtensionAdjunction A B) : F.hom_isomorphism := by
  sorry

end Sdga
