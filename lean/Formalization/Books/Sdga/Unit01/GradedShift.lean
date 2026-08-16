import Formalization.Books.Sdga.Unit01.Core

/-! # 11. Shift functors on sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedShiftFamily {S : RingedSite.{u,v} R}
    (M : GradedFamily S) (k : ℤ) : GradedFamily S := shiftFamily M k

def gradedShift {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M : GradedModule S A) (k : ℤ) : GradedModule S A where
  component := gradedShiftFamily M.component k
  action n m U x a := cast
    (congrArg (fun q : ℤ => M.component q U)
      (by
        calc
          (n + k) + m = n + (k + m) := Int.add_assoc n k m
          _ = n + (m + k) := congrArg (fun q : ℤ => n + q) (Int.add_comm k m)
          _ = (n + m) + k := (Int.add_assoc n m k).symm))
    (M.action (n + k) m U x a)
  laws := M.laws

structure GradedShiftData {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  shift : ℤ → GradedModule S A → GradedModule S A
  component_formula : Prop
  composition : Prop
  hom_shift : Prop

theorem graded_shift_composition
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (D : GradedShiftData A) : D.composition ∧ D.hom_shift := by
  sorry

theorem lemma_gm_grothendieck_abelian (S : RingedSite.{u,v} R)
    (A : GradedAlgebra S) :
    Nonempty (GrothendieckCategoryStatement (GradedModuleCategory S A)) := by
  sorry

end Sdga
