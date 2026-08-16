import Formalization.«Books.SpacesCohomology».Unit01.HigherVanishing

/-!
# Vanishing for higher direct images
-/

namespace Formalization.«Books.SpacesCohomology».Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

def higherDirectImageVanishesAfter
    {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) (n : ℕ) : Prop :=
  ∀ (Y' : AlgebraicSpace.{u}) (g : SpaceHom Y' Y)
    (F' : SheafObj (baseChange f g)), IsQuasiCoherent F' →
    ∀ i : ℕ, n ≤ i →
      higherDirectImage i (baseChangeTarget f g) F' = zeroSheaf Y'

theorem higher_direct_images_uniform_vanishing
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hqc : IsQuasiCompact f) (hqs : IsQuasiSeparated f)
    (hY : IsQuasiCompact (𝟙 Y : SpaceHom Y Y)) :
    ∃ n : ℕ, higherDirectImageVanishesAfter f n := by
  sorry

theorem affine_higher_direct_image_vanishing
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hAffine : IsAffine f)
    (F : SheafObj X) (hF : IsQuasiCoherent F) :
    ∀ i : ℕ, 0 < i → higherDirectImage i f F = zeroSheaf Y := by
  sorry

theorem relative_affine_cohomology
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hAffine : IsAffine f)
    (F : SheafObj X) (hF : IsQuasiCoherent F) (i : ℤ) :
    CohomologyComparison X Y F (pushforwardSheaf f F) i i := by
  sorry

end Formalization.«Books.SpacesCohomology».Unit01
