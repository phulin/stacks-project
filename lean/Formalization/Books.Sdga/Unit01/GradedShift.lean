import Formalization.«Books.Sdga».Unit01.Core

/-! # 11. Shift functors on sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedShiftFamily {S : RingedSite.{u,v} R}
    (M : GradedFamily S) (k : ℤ) : GradedFamily S := shiftFamily M k

structure GradedShiftData {S : RingedSite.{u,v} R}
    (A : GradedAlgebra S) where
  shift : ℤ → GradedModule S A → GradedFamily S
  component_formula : Prop
  composition : Prop
  hom_shift : Prop

theorem graded_shift_composition
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (D : GradedShiftData A) : D.composition ∧ D.hom_shift := by
  sorry

theorem lemma_gm_grothendieck_abelian (S : RingedSite.{u,v} R)
    (A : GradedAlgebra S) :
    GrothendieckCategoryStatement (GradedModuleCategory S A) := by
  sorry

end Sdga
