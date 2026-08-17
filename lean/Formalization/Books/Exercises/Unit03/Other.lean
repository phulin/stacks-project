import Formalization.Books.Homology.Unit03.PreadditiveAndAdditiveCategories
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Data.ZMod.Basic

/-!
# Exercises, Chapter 3: another additive category

The category of abelian groups, represented canonically as `ModuleCat ℤ`, is
an example with all kernels and cokernels that is different from the two
categories in the preceding exercises.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Formalization.Books.Exercises.Unit03

/- The standard additive-category structure on the category of abelian
   groups. -/
@[instance_reducible]
def abelianGroupsAdditiveCategory :
    Formalization.Books.Homology.Unit03.AdditiveCategory (ModuleCat ℤ) where
  toPreadditive := inferInstance
  toHasFiniteProducts := inferInstance

theorem abelianGroups_additive :
    Nonempty
      (Formalization.Books.Homology.Unit03.AdditiveCategory (ModuleCat ℤ)) :=
  ⟨abelianGroupsAdditiveCategory⟩

theorem abelianGroups_has_kernels_and_cokernels :
    HasKernels (ModuleCat ℤ) ∧ HasCokernels (ModuleCat ℤ) :=
  ⟨ModuleCat.hasKernels_moduleCat, ModuleCat.hasCokernels_moduleCat⟩

/-- A torsion abelian group, which is not an object of the preceding
torsion-free category. -/
def exampleTorsionAbelianGroup : ModuleCat ℤ :=
  ModuleCat.of ℤ (ZMod 2)

theorem exampleTorsionAbelianGroup_not_torsionFree :
    ¬ Module.IsTorsionFree ℤ exampleTorsionAbelianGroup := by
  intro h
  have hzero : (2 : ℤ) • (1 : ZMod 2) = 0 := by
    change (2 : ZMod 2) = 0
    decide
  have hcases :=
    (Module.isTorsionFree_iff_smul_eq_zero (R := ℤ)
      (M := ZMod 2)).mp h 2 1 hzero
  rcases hcases with htwo | hone
  · exact (by decide : (2 : ℤ) ≠ 0) htwo
  · exact (by decide : (1 : ZMod 2) ≠ 0) hone

end Formalization.Books.Exercises.Unit03
