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
  K L : DGModule S A
  f : DGModuleHom K L
  cone : ConeData K L f
  distinguished : Prop

def cone {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {K L : DGModule S A} {f : DGModuleHom K L} (C : ConeData K L f) := C.component

theorem lemma_axioms_AB {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (I : HomotopyABInterface A) : I.axiom_A ∧ I.axiom_B := by
  sorry

theorem lemma_axiom_C {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (T : DistinguishedTriangleData) : T.distinguished := by
  exact T.distinguished

theorem proposition_homotopy_category_triangulated
    {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (H : HomotopyCategoryData S A) :
    TriangulatedCategoryStatement (DGModuleCategory S A) := by
  sorry

theorem remark_cone_identity {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {K L : DGModule S A} {f : DGModuleHom K L} (C : ConeData K L f) :
    C.component_eq := by
  exact C.component_eq

theorem lemma_dgm_grothendieck_abelian (S : RingedSite.{u,v} R)
    (A : DGAlgebra S) :
    GrothendieckCategoryStatement (DGModuleCategory S A) := by
  sorry

end Sdga
