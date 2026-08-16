import Formalization.«Books.Sdga».Unit01.Core

/-! # 5. The graded category of sheaves of graded modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def gradedCategoryHom {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    (M N : GradedModule S A) (k : ℤ) := HomogeneousMap M N k

def gradedCategoryComposition {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N P : GradedModule S A} {k l : ℤ}
    (g : gradedCategoryHom N P l) (f : gradedCategoryHom M N k) :=
  HomogeneousMap.comp g f

theorem graded_category_hom_is_module_map
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N : GradedModule S A} {k : ℤ} (f : gradedCategoryHom M N k) :
    HomogeneousMap.isModuleMap f := by
  exact f.isModuleMap

theorem graded_category_composition_degree
    {S : RingedSite.{u,v} R} {A : GradedAlgebra S}
    {M N P : GradedModule S A} {k l : ℤ}
    (g : gradedCategoryHom N P l) (f : gradedCategoryHom M N k) :
    gradedCategoryComposition g f = HomogeneousMap.comp g f := by
  rfl

end Sdga
