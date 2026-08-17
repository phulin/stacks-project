import Formalization.Books.SpacesCohomology.Unit01.Limits
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Ring.Basic

/-!
# Vanishing of cohomology
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

structure VanishingSituation (X : AlgebraicSpace.{u}) (A : Type u)
    [CommRing A] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] where
  quasi_compact : IsQuasiCompact (𝟙 X : SpaceHom X X)
  quasi_separated : IsQuasiSeparated (𝟙 X : SpaceHom X X)
  h1_vanishes : ∀ (F : SheafObj X), IsQuasiCoherent F →
    Subsingleton (CohomologyGroup X F 1)
  affine_target : AlgebraicSpace.{u}
  p : SpaceHom X affine_target
  affine_target_is_scheme : IsScheme affine_target
  global_sections_identification : Prop
  zero_locus : A → Set X

structure TensorSectionsData {X : AlgebraicSpace.{u}} {A : Type u}
    [CommRing A] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A)
    (M : Type u) [AddCommGroup M] [Module A M] where
  tensor : SheafObj X
  tensor_property : Prop
  pushforward_property : Prop
  sections_identification : Nonempty (Sections X tensor ≃+ M)

theorem vanishing_compute
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    Nonempty (TensorSectionsData V M) := by
  sorry

def AffineH1Vanishes (X : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] : Prop :=
  ∀ (F : SheafObj X), IsQuasiCoherent F →
    Subsingleton (CohomologyGroup X F 1)

structure VanishingAffineBaseChange {X : AlgebraicSpace.{u}} {A : Type u}
    [CommRing A] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A)
    where
  X' : AlgebraicSpace.{u}
  g : SpaceHom X' X
  affine : IsAffine g
  h1 : AffineH1Vanishes X'
  global_sections : Prop

structure VanishingAlgebraBaseChange {X : AlgebraicSpace.{u}} {A : Type u} (A' : Type u)
    [CommRing A] [CommRing A'] [Algebra A A']
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) where
  X' : AlgebraicSpace.{u}
  g : SpaceHom X' X
  affine : IsAffine g
  global_sections : Prop

theorem vanishing_base_change
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A)
    (X' : AlgebraicSpace.{u}) (g : SpaceHom X' X) (hg : IsAffine g) :
    AffineH1Vanishes X' := by
  sorry

theorem vanishing_algebra_base_change
    {X : AlgebraicSpace.{u}} {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) :
    Nonempty (VanishingAlgebraBaseChange A' V) := by
  sorry

theorem vanishing_separate_closed
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) (Z₀ Z₁ : ClosedSubspace X)
    (hdisjoint : Disjoint (Set.range Z₀.inclusion) (Set.range Z₁.inclusion)) :
    ∃ a : A, Set.range Z₀.inclusion ⊆ V.zero_locus a ∧
      Set.range Z₁.inclusion ⊆ V.zero_locus (a - 1) := by
  sorry

theorem vanishing_universally_injective
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) :
    IsUniversallyInjective V.p := by
  sorry

theorem vanishing_separated
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) :
    IsSeparated V.p := by
  sorry

theorem proposition_vanishing_affine
    {X : AlgebraicSpace.{u}} {A : Type u} [CommRing A]
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (V : VanishingSituation X A) :
    IsScheme X ∧ IsAffine V.p := by
  sorry

theorem noetherian_h1_zero
    (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (hX : IsNoetherian X)
    (h : ∀ F : SheafObj X, IsCoherentModule X F →
      Subsingleton (CohomologyGroup X F 1)) :
    IsScheme X ∧ IsAffine (𝟙 X : SpaceHom X X) := by
  sorry

theorem noetherian_h1_zero_invertible
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (L : SheafObj X)
    (hX : IsNoetherian X) (hL : IsInvertible L)
    (h : ∀ F : SheafObj X, IsCoherentModule X F →
      ∃ n : ℕ, 1 ≤ n ∧
        Subsingleton (CohomologyGroup X (tensorSheaf X F
          (tensorPowerSheaf X L n)) 1)) :
    IsScheme X ∧ IsAmple L := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
