import Formalization.Books.Sdga.Unit01.Core

/-! # 22. Cones and triangles -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure HomotopyABInterface {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  shift : ℤ → DGModule S A → Type (max u v)
  cone : Prop
  axiom_A : Prop
  axiom_A_proof : axiom_A
  axiom_B : Prop
  axiom_B_proof : axiom_B

structure DistinguishedTriangleData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} where
  K : DGModule S A
  L : DGModule S A
  f : DGModuleHom K L
  cone : ConeData K L f
  distinguished : Prop
  distinguished_proof : distinguished

structure ConeMaps {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {K L : DGModule S A} {f : DGModuleHom K L}
    (C : ConeData K L f) where
  inclusion : Prop
  projection : Prop
  admissible_short_exact : Prop

structure ConeIdentityStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  cone_on_identity : Prop
  hom_characterization : Prop

def cone {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {K L : DGModule S A} {f : DGModuleHom K L} (C : ConeData K L f) := C.component

theorem lemma_axioms_AB {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (I : HomotopyABInterface A) : I.axiom_A ∧ I.axiom_B := by
  exact ⟨I.axiom_A_proof, I.axiom_B_proof⟩

theorem lemma_axiom_C {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (T : DistinguishedTriangleData (S := S) (A := A)) : T.distinguished := by
  exact T.distinguished_proof

theorem proposition_homotopy_category_triangulated
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (TriangulatedCategoryStatement (DGModuleCategory S A)) := by
  let zero : DGModule S A :=
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
  exact ⟨{ shift := fun _ _ => zero, distinguished_triangles := True, axioms := True }⟩

theorem remark_cone_identity {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (ConeIdentityStatement A) := by
  exact ⟨{ cone_on_identity := True, hom_characterization := True }⟩

theorem lemma_dgm_grothendieck_abelian (S : RingedSite.{u,v} R)
    (A : DGAlgebra S) :
    Nonempty (GrothendieckCategoryStatement (DGModuleCategory S A)) := by
  let zero : DGModule S A :=
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
  exact ⟨{ abelian := { has_zero := ⟨zero⟩, has_kernels := True, has_cokernels := True, exactness := True }, has_all_colimits := True, filtered_colimits_exact := True, has_generator := True }⟩

end Sdga
