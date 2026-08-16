import Formalization.«Books.Sdga».Unit01.Core

/-! # 20. Shift functors on sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The source's shift construction is represented by its component and
differential data. -/
def dgShift {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) (k : ℤ) := ShiftedDGModule M k

structure DGShiftFunctorData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  shift : ℤ → DGModule S A → Type (max u v)
  component_formula : Prop
  composition : Prop
  hom_shift : Prop

theorem dg_shift_functor_laws
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (D : DGShiftFunctorData A) : D.component_formula ∧ D.composition ∧ D.hom_shift := by
  sorry

end Sdga
