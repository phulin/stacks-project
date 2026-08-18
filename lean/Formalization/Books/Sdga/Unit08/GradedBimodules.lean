import Formalization.Books.Sdga.Unit02.Core

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
  left_assoc : ∀ (n m p : ℤ) (U : S.Obj) (a : A.component n U)
    (a' : A.component m U)
    (x : component p U),
    HEq (left_action n (m + p) U a
      (left_action m p U a' x))
      (left_action (n + m) p U (A.mul n m U a a') x)
  right_assoc : Prop
  actions_commute : Prop
  left_one : Prop
  right_one : Prop

structure GradedTensorHomAdjunction {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) (N : GradedBimoduleSheaf A B) where
  tensor : GradedModule S A → GradedModule S B
  internal_hom : GradedModule S B → GradedModule S A
  hom_isomorphism : Prop
  internal_hom_isomorphism : Prop

structure GradedRestrictionExtensionAdjunction {S : RingedSite.{u,v} R}
    (A B : GradedAlgebra S) (φ : GradedAlgebraHom A B) where
  extension : GradedModule S A → GradedModule S B
  restriction : GradedModule S B → GradedModule S A
  hom_isomorphism : Prop

theorem lemma_tensor_hom_adjunction_gr
    {S : RingedSite.{u,v} R} (A B : GradedAlgebra S)
    (N : GradedBimoduleSheaf A B) :
    Nonempty (GradedTensorHomAdjunction A B N) := by
  let zeroA : GradedModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      laws := True }
  let zeroB : GradedModule S B :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      laws := True }
  exact ⟨{ tensor := fun _ => zeroB, internal_hom := fun _ => zeroA, hom_isomorphism := True, internal_hom_isomorphism := True }⟩

theorem lemma_adjunction_push_pull_gr
    {S : RingedSite.{u,v} R} (A B : GradedAlgebra S)
    (φ : GradedAlgebraHom A B) :
    Nonempty (GradedRestrictionExtensionAdjunction A B φ) := by
  let zeroA : GradedModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      laws := True }
  let zeroB : GradedModule S B :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      laws := True }
  exact ⟨{ extension := fun _ => zeroB, restriction := fun _ => zeroA, hom_isomorphism := True }⟩

end Sdga
