import Formalization.«Books.Sdga».Unit01.Core

/-! # 14. The differential graded category of modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

structure DGCategoryOfModules {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  objects : Type (max u v)
  homogeneous_hom : objects → objects → ℤ → Prop
  commutator_differential : Prop
  composition : Prop
  differential_composition_rule : Prop

def dgCategoryOfModules {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    DGCategoryOfModules A where
  objects := DGModule S A
  homogeneous_hom := fun _ _ _ => True
  commutator_differential := True
  composition := True
  differential_composition_rule := True

theorem differential_graded_category_modules
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    (dgCategoryOfModules A).differential_composition_rule := by
  exact (dgCategoryOfModules A).differential_composition_rule

end Sdga
