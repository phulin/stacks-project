import Formalization.«Books.Sdga».Unit01.Core

/-! # 22. Cones and triangles -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure HomotopyABInterface {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  shift : ℤ → DGModule S A → Type (max u v)
  cone : Prop
  axiom_A : Prop
  axiom_B : Prop

structure DistinguishedTriangleData {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} where
  K : DGModule S A
  L : DGModule S A
  f : DGModuleHom K L
  cone : ConeData K L f
  distinguished : Prop

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
  sorry

theorem lemma_axiom_C {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (T : DistinguishedTriangleData (S := S) (A := A)) : T.distinguished := by
  sorry

theorem proposition_homotopy_category_triangulated
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (TriangulatedCategoryStatement (DGModuleCategory S A)) := by
  sorry

theorem remark_cone_identity {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    Nonempty (ConeIdentityStatement A) := by
  sorry

theorem lemma_dgm_grothendieck_abelian (S : RingedSite.{u,v} R)
    (A : DGAlgebra S) :
    Nonempty (GrothendieckCategoryStatement (DGModuleCategory S A)) := by
  sorry

end Sdga
