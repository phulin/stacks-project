import Formalization.Books.SpacesCohomology.Unit01.Ample
import Mathlib.RingTheory.Ideal.Basic

/-!
# The theorem on formal functions
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure FormalFunctionsSituation (A : Type u) (X Y : AlgebraicSpace.{u})
    [CommRing A] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  noetherian : Prop
  I : Ideal A
  f : SpaceHom X Y
  target_is_spectrum : Prop
  proper : IsProper f
  F : SheafObj X
  coherent : IsCoherentModule X F
  power : ℕ → SheafObj X
  power_description : Prop
  quotient : ℕ → SheafObj X
  quotient_description : Prop

def FormalPowerCohomology {A : Type u} {X Y : AlgebraicSpace.{u}}
    [CommRing A] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (p n : ℕ) : Type u :=
  CohomologyGroup X (V.power n) p

structure FiniteGradedCohomologyPowers (A : Type u)
    [CommRing A] where
  graded_algebra : Type u
  graded_module : Type u
  graded_algebra_property : Prop
  module_property : Prop
  finite : Prop

theorem cohomology_powers_ideal_times_F
    {A : Type u} {X Y : AlgebraicSpace.{u}} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (p : ℕ) :
    Nonempty (FiniteGradedCohomologyPowers A) := by
  sorry

structure FormalFunctionsPowerApplication where
  c : ℕ
  multiplication_surjective : Prop
  image_containment : Prop

theorem cohomology_powers_ideal_application
    {A : Type u} {X Y : AlgebraicSpace.{u}} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (p : ℕ) :
    Nonempty (FormalFunctionsPowerApplication) := by
  sorry

structure MittagLefflerFormalFunctionsStatement where
  c₁ : ℕ
  kernel_bound : Prop
  mittag_leffler : Prop
  c₂ : ℕ → ℕ
  c₂_bound : ∀ n, n ≤ c₂ n
  stable_image : Prop

theorem ML_cohomology_powers_ideal
    {A : Type u} {X Y : AlgebraicSpace.{u}} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (p : ℕ) :
    Nonempty (MittagLefflerFormalFunctionsStatement) := by
  sorry

structure FormalFunctionsLimitStatement where
  completion : Type u
  inverse_limit : Type u
  completion_group : AddCommGroup completion
  inverse_limit_group : AddCommGroup inverse_limit
  comparison : Prop
  topological_statement : Prop

theorem theorem_formal_functions
    {A : Type u} {X Y : AlgebraicSpace.{u}} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (p : ℕ) :
    Nonempty (FormalFunctionsLimitStatement) := by
  sorry

structure CompleteFormalFunctionsStatement where
  complete_base : Prop
  identification : Prop

theorem spell_out_theorem_formal_functions
    {A : Type u} {X Y : AlgebraicSpace.{u}} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : FormalFunctionsSituation A X Y) (hcomplete : Prop) (p : ℕ) :
    Nonempty (CompleteFormalFunctionsStatement) := by
  sorry

structure StalkFormalFunctionsStatement (Y : AlgebraicSpace.{u})
    (y : Y) [AlgebraicSpaceCohomology.{u}] where
  completed_stalk : Type u
  inverse_limit : Type u
  completed_stalk_group : AddCommGroup completed_stalk
  inverse_limit_group : AddCommGroup inverse_limit
  identification : Prop
  module_structure : Prop

theorem formal_functions_stalk
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X) (y : Y)
    (hY : IsLocallyNoetherian Y) (hf : IsProper f)
    (hF : IsCoherentModule X F) (p : ℕ) :
    Nonempty (StalkFormalFunctionsStatement Y y) := by
  sorry

theorem higher_direct_images_zero_finite_fibre
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X) (y : Y)
    (hY : IsLocallyNoetherian Y) (hf : IsProper f)
    (hF : IsCoherentModule X F)
    (hdiscrete : IsDiscrete (FibreSpace f y)) :
    ∀ p : ℕ, 0 < p → Subsingleton (Stalk Y (higherDirectImage p f F) y) := by
  sorry

theorem higher_direct_images_zero_above_dimension_fibre
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X) (y : Y)
    (hY : IsLocallyNoetherian Y) (hf : IsProper f)
    (hF : IsCoherentModule X F) (d : ℕ)
    (hdim : SpaceDimension (FibreSpace f y) = d) :
    ∀ p : ℕ, d < p → Subsingleton (Stalk Y (higherDirectImage p f F) y) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
