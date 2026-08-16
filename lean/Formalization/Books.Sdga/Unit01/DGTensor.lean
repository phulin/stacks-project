import Formalization.«Books.Sdga».Unit01.Core

/-! # 15. Tensor product for sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def dgTensorObject {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (T : DGTensorModel M N) : GradedFamily S :=
  dgTensorProduct T

structure DGTensorDifferentialStatement {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} {M N : DGModule S A} (T : DGTensorModel M N) where
  graded_tensor : T.balanced
  Leibniz : T.leibniz
  square_zero : T.differential_squared

theorem dg_tensor_differential
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} (T : DGTensorModel M N) :
    Nonempty (DGTensorDifferentialStatement T) := by
  sorry

end Sdga
