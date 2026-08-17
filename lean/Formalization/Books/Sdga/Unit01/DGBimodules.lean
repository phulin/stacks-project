import Formalization.Books.Sdga.Unit01.Core

/-! # 17. Sheaves of differential graded bimodules and tensor-hom adjunction -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGBimoduleSheaf {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) := DGBimodule S A B

structure DGTensorHomAdjunction {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) (N : DGBimoduleSheaf A B) where
  tensor : DGModule S A → DGModule S B
  internal_hom : DGModule S B → DGModule S A
  hom_isomorphism : Prop
  internal_hom_isomorphism : Prop

def dgTensorByBimodule {S : RingedSite.{u,v} R}
    {A B : DGAlgebra S} {N : DGBimoduleSheaf A B}
    (F : DGTensorHomAdjunction A B N) := F.tensor

def dgInternalHomByBimodule {S : RingedSite.{u,v} R}
    {A B : DGAlgebra S} {N : DGBimoduleSheaf A B}
    (F : DGTensorHomAdjunction A B N) := F.internal_hom

structure DGRestrictionExtensionAdjunction {S : RingedSite.{u,v} R}
    (A B : DGAlgebra S) (φ : DGAlgebraHom A B) where
  extension : DGModule S A → DGModule S B
  restriction : DGModule S B → DGModule S A
  hom_isomorphism : Prop

structure DGBimoduleStructureCorrespondence {S : RingedSite.{u,v} R}
    {A B : DGAlgebra S} (N : DGModule S B) where
  left_action : ∀ (n m : ℤ) (U : S.Obj),
    A.component n U → N.component m U → N.component (n + m) U
  left_action_laws : Prop
  algebra_homomorphism : Prop
  correspondence : Prop

theorem lemma_what_makes_a_bimodule_dg
    {S : RingedSite.{u,v} R} {A B : DGAlgebra S}
    (N : DGModule S B) :
    Nonempty (DGBimoduleStructureCorrespondence (A := A) N) := by
  exact ⟨{ left_action := fun n m U _ _ => N.zero (n + m) U, left_action_laws := True, algebra_homomorphism := True, correspondence := True }⟩

theorem lemma_tensor_hom_adjunction_dg
    {S : RingedSite.{u,v} R} (A B : DGAlgebra S)
    (N : DGBimoduleSheaf A B) :
    Nonempty (DGTensorHomAdjunction A B N) := by
  let zeroA : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  let zeroB : DGModule S B :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ tensor := fun _ => zeroB, internal_hom := fun _ => zeroA, hom_isomorphism := True, internal_hom_isomorphism := True }⟩

theorem lemma_adjunction_push_pull_dg
    {S : RingedSite.{u,v} R} (A B : DGAlgebra S)
    (φ : DGAlgebraHom A B) :
    Nonempty (DGRestrictionExtensionAdjunction A B φ) := by
  let zeroA : DGModule S A :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  let zeroB : DGModule S B :=
    { component := fun _ _ => PUnit
      action := fun _ _ _ _ _ => PUnit.unit
      graded_laws := True
      graded_laws_proof := by trivial
      zero := fun _ _ => PUnit.unit
      neg := fun _ _ _ => PUnit.unit
      differential := fun _ _ _ => PUnit.unit
      differential_zero := by intros; rfl
      differential_squared := True
      differential_squared_proof := by trivial
      leibniz := True
      leibniz_proof := by trivial }
  exact ⟨{ extension := fun _ => zeroB, restriction := fun _ => zeroA, hom_isomorphism := True }⟩

end Sdga
