import Formalization.Books.SpacesCohomology.Unit01.Valuative
import Mathlib.Algebra.Ring.Basic

/-!
# Higher direct images of coherent sheaves
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure ProjectiveTwistingData (X Y : AlgebraicSpace.{u})
    (f : SpaceHom X Y) [AlgebraicSpaceTheory.{u}]
    [AlgebraicSpaceCohomology.{u}] where
  projective_space : AlgebraicSpace.{u}
  embedding : SpaceHom X projective_space
  projective_map : SpaceHom projective_space Y
  commutative : Prop
  closed_embedding : IsClosedImmersion embedding
  projective : IsProjective projective_map
  proper : IsProper f
  Y_noetherian : IsNoetherian Y
  L : SheafObj X
  L_is_pullback_of_O1 : Prop

def HigherDirectImageVanishes (X Y : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (f : SpaceHom X Y) (F : SheafObj X)
    (L : SheafObj X) (d p : ℕ) : Prop :=
  Subsingleton (Sections Y
    (higherDirectImage p f (tensorSheaf X F (tensorPowerSheaf X L d))))

theorem kill_by_twisting
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X)
    (D : ProjectiveTwistingData X Y f)
    (hF : IsCoherentModule X F) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ p : ℕ, 0 < p →
      HigherDirectImageVanishes X Y f F D.L d p := by
  sorry

theorem proper_pushforward_coherent
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X)
    (hf : IsProper f) (hY : IsLocallyNoetherian Y)
    (hF : IsCoherentModule X F) :
    IsCoherentModule Y (pushforwardSheaf f F) ∧
      ∀ p : ℕ, 0 < p → IsCoherentModule Y (higherDirectImage p f F) := by
  sorry

structure FiniteAModuleStatement (A M : Type u) [CommRing A]
    [AddCommGroup M] where
  module : Module A M
  finite : Prop

theorem proper_over_affine_cohomology_finite
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (A : Type u) [CommRing A]
    (f : SpaceHom X Y) (F : SheafObj X)
    (hA : Prop) (hY : IsScheme Y) (hY_is_spectrum : Prop) (hf : IsProper f)
    (hF : IsCoherentModule X F) :
    ∀ p : ℕ, Nonempty (FiniteAModuleStatement A (CohomologyGroup X F p)) := by
  sorry

structure GradedFiniteData (A B : Type u) [CommRing A]
    [AlgebraicSpaceCohomology.{u}] where
  graded_algebra : Prop
  finite_type_over_A : Prop
  X : AlgebraicSpace.{u}
  Y : AlgebraicSpace.{u}
  f : SpaceHom X Y
  proper : Prop
  sheaf_algebra : SheafObj X
  sheaf_module : SheafObj X
  graded_module : Prop
  finite_type_module : Prop

structure FiniteGradedModuleStatement (B M : Type u) where
  graded_module : Prop
  finite : Prop

theorem graded_finiteness
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (A B : Type u) [CommRing A] (D : GradedFiniteData A B) :
    ∀ p : ℕ, Nonempty
      (FiniteGradedModuleStatement B (CohomologyGroup D.X D.sheaf_module p)) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
