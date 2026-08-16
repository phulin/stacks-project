import Formalization.«Books.Sdga».Unit01.Core

/-! # 8. Sheaves of graded bimodules and tensor-hom adjunction -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure GradedBimoduleSheaf {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) where
  component : GradedFamily S
  left_action : ∀ (n m : ℤ) (U : S.Obj),
    A.component n U → component m U → component (n + m) U
  right_action : ∀ (n m : ℤ) (U : S.Obj),
    component n U → B.component m U → component (n + m) U
  laws : Prop

structure GradedTensorHomAdjunction {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) where
  tensor : GradedModule S A → GradedModule S B
  internal_hom : GradedModule S B → GradedModule S A
  hom_isomorphism : Prop
  internal_hom_isomorphism : Prop

structure GradedRestrictionExtensionAdjunction {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) where
  extension : GradedModule S A → GradedModule S B
  restriction : GradedModule S B → GradedModule S A
  hom_isomorphism : Prop

theorem definition_bimodule {S : RingedSite.{u,v} R}
    {A B : GradedAlgebra S} (M : GradedBimoduleSheaf A B) : M.laws := by
  exact M.laws

theorem lemma_tensor_hom_adjunction_gr
    {S : RingedSite.{u,v} R} (A B : GradedAlgebra S)
    (F : GradedTensorHomAdjunction A B) :
    F.hom_isomorphism ∧ F.internal_hom_isomorphism := by
  sorry

theorem lemma_adjunction_push_pull_gr
    {S : RingedSite.{u,v} R} (A B : GradedAlgebra S)
    (F : GradedRestrictionExtensionAdjunction A B) :
    F.hom_isomorphism := by
  sorry

end Sdga
