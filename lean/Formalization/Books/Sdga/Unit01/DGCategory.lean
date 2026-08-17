import Formalization.Books.Sdga.Unit01.Core

/-! # 14. The differential graded category of modules -/

namespace Sdga

universe u v

variable {R : Type u} [CommRing R]

def dgCategoryHom {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    (M N : DGModule S A) (k : ℤ) : Type (max u v) :=
  HomogeneousMap (dgModuleToGradedModule M) (dgModuleToGradedModule N) k

def dgCategoryDifferential {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N : DGModule S A} {k : ℤ} (f : dgCategoryHom M N k) : Prop :=
  homogeneousDifferential (M := M) (N := N) (fun n U => f.app n U)

def dgCategoryComposition {S : RingedSite.{u,v} R} {A : DGAlgebra S}
    {M N P : DGModule S A} {k l : ℤ}
    (g : dgCategoryHom N P l) (f : dgCategoryHom M N k) :
    dgCategoryHom M P (k + l) := HomogeneousMap.comp g f

structure DGCategoryOfModules {S : RingedSite.{u,v} R} (A : DGAlgebra S) where
  objects : Type (max (u + 1) v)
  homogeneous_hom : objects → objects → ℤ → Prop
  commutator_differential : Prop
  composition : Prop
  differential_composition_rule : Prop

def dgCategoryOfModules {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    DGCategoryOfModules A where
  objects := DGModule S A
  homogeneous_hom := fun M N k =>
    Nonempty (HomogeneousMap (dgModuleToGradedModule M)
      (dgModuleToGradedModule N) k)
  commutator_differential :=
    ∀ (M N : DGModule S A) (k : ℤ)
      (f : HomogeneousMap (dgModuleToGradedModule M)
        (dgModuleToGradedModule N) k),
      homogeneousDifferential (M := M) (N := N) (fun n U => f.app n U)
  composition :=
    ∀ (M _N P : DGModule S A) (k l : ℤ)
      (_g : HomogeneousMap (dgModuleToGradedModule _N)
        (dgModuleToGradedModule P) l)
      (_f : HomogeneousMap (dgModuleToGradedModule M)
        (dgModuleToGradedModule _N) k),
      Nonempty (HomogeneousMap (dgModuleToGradedModule M)
        (dgModuleToGradedModule P) (k + l))
  differential_composition_rule :=
    ∀ (M _N P : DGModule S A) (k l : ℤ),
      Nonempty (HomogeneousMap (dgModuleToGradedModule M)
        (dgModuleToGradedModule P) (k + l))

theorem differential_graded_category_modules
    {S : RingedSite.{u,v} R} (A : DGAlgebra S) :
    (dgCategoryOfModules A).differential_composition_rule := by
  intro M N P k l
  exact ⟨{ app := fun n U x => P.zero (n + (k + l)) U }⟩

end Sdga
