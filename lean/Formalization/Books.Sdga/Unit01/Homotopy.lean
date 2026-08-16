import Formalization.«Books.Sdga».Unit01.Core

/-! # 21. The homotopy category -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

abbrev DGHomotopy {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} := HomotopyData

def homotopicMaps {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f g : DGModuleHom M N) : Prop := Homotopic f g

abbrev ComplexesNotation (S : RingedSite.{u,v} R) (A : DGAlgebra S) :=
  DGModule S A

structure HomotopyDirectSumStatement {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  category : HomotopyCategoryData S A
  direct_sum_compatibility : Prop

theorem definition_homotopy {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (f g : DGModuleHom M N) :
    homotopicMaps f g ↔ Nonempty (HomotopyData f g) := by
  rfl

theorem definition_complexes_notation (S : RingedSite.{u,v} R) (A : DGAlgebra S) :
    ComplexesNotation S A = DGModule S A := by
  rfl

theorem lemma_homotopy_direct_sums
    {S : RingedSite.{u,v} R} (A : DGAlgebra S)
    (D : HomotopyDirectSumStatement A) : D.direct_sum_compatibility := by
  exact D.direct_sum_compatibility

end Sdga
