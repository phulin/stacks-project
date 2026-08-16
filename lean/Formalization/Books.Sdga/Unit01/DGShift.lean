import Formalization.«Books.Sdga».Unit01.Core

/-! # 20. Shift functors on sheaves of differential graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

/-- The source's shift construction is represented by its component and
differential data. -/
def dgShiftFamily {S : RingedSite.{u,v} R}
    {A : DGAlgebra S} (M : DGModule S A) (k : ℤ) : GradedFamily S :=
  shiftFamily M.component k

def dgShift {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M : DGModule S A) (k : ℤ) : ShiftedDGModule M k where
  component := dgShiftFamily M k
  component_eq := rfl
  differential n U x := cast
    (congrArg (fun q : ℤ => M.component q U)
      (by
        calc
          (n + k) + 1 = n + (k + 1) := Int.add_assoc n k 1
          _ = n + (1 + k) := congrArg (fun q => n + q) (Int.add_comm k 1)
          _ = (n + 1) + k := (Int.add_assoc n 1 k).symm))
    (if k % 2 = 0 then
      M.differential (n + k) U x
    else
      M.neg (n + k + 1) U (M.differential (n + k) U x))
  differential_squared := M.differential_squared

structure DGShiftFunctorData {S : RingedSite.{u,v} R}
    (A : DGAlgebra S) where
  shift : ℤ → DGModule S A → DGModule S A
  component_formula : Prop
  composition : Prop
  hom_shift : Prop

theorem dg_shift_functor_laws
    {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (D : DGShiftFunctorData A) : D.component_formula ∧ D.composition ∧ D.hom_shift := by
  sorry

end Sdga
