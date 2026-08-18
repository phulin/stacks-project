import Formalization.Books.Sdga.Unit02.Core

/-! # 6. Tensor product for sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedTensorObject {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M : GradedModule S A} {N : LeftGradedModule S A}
  (T : GradedTensorModel M N) : GradedFamily S := gradedTensorProduct T

def gradedTensorComponent {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M : GradedModule S A} {N : LeftGradedModule S A}
    (T : GradedTensorModel M N) (n : ℤ) (U : S.Obj) : Type u :=
  T.component n U

def gradedTensorBalancingRelation {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M : GradedModule S A} {N : LeftGradedModule S A}
    (T : GradedTensorModel M N) : Prop := T.balanced

structure GradedTensorFunctorData {S : RingedSite.{u,v} R}
    {A : GradedAlgebra S} (N : LeftGradedModule S A) where
  object : GradedModule S A → GradedFamily S
  map_on_homogeneous_maps : Prop

structure GradedTensorUniversalProperty {S : RingedSite.{u,v} R}
    {A : GradedAlgebra S} {M : GradedModule S A} {N : LeftGradedModule S A}
    (T : GradedTensorModel M N) where
  balanced : T.balanced
  universal : T.universal

theorem graded_tensor_product_universal
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M : GradedModule S A} {N : LeftGradedModule S A}
    (T : GradedTensorModel M N) : Nonempty (GradedTensorUniversalProperty T) := by
  exact ⟨{ balanced := T.balanced_proof, universal := T.universal_proof }⟩

end Sdga
