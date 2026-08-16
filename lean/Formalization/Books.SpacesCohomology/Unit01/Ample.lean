import Formalization.«Books.SpacesCohomology».Unit01.ProperPushforward

/-!
# Ample invertible sheaves and cohomology
-/

namespace Formalization.«Books.SpacesCohomology».Unit01

universe u

def AmpleVanishingConditionOne (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X) : Prop :=
  IsScheme X ∧ IsAmple L

def AmpleVanishingConditionTwo (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X) : Prop :=
  ∀ F : SheafObj X, IsCoherentModule X F →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℤ, 0 < p →
      CohomologyVanishes X (tensorSheaf X F (tensorPowerSheaf X L n)) p

def AmpleVanishingConditionThree (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X) : Prop :=
  ∀ F : SheafObj X, IsCoherentModule X F →
    ∃ n : ℕ, 1 ≤ n ∧
      CohomologyVanishes X (tensorSheaf X F (tensorPowerSheaf X L n)) 1

def AmpleVanishingCriterion (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X) : Prop :=
  AmpleVanishingConditionOne X L ↔
    (AmpleVanishingConditionTwo X L ∧ AmpleVanishingConditionThree X L)

theorem vanishing_gives_ample
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X S : AlgebraicSpace.{u}) (p : SpaceHom X S) (L : SheafObj X)
    (hS : IsScheme S) (hS_noetherian : Prop) (hp : IsProper p)
    (hL : IsInvertible L) :
    AmpleVanishingCriterion X L := by
  sorry

structure FiniteSurjectiveAmpleStatement (X Y : AlgebraicSpace.{u})
    (f : SpaceHom Y X) [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X) where
  finite : IsFinite f
  surjective : IsSurjective f
  proper_over_base : Prop
  equivalence :
    (IsScheme X ∧ IsAmple L) ↔
      (IsScheme Y ∧ IsAmple (pullbackSheaf f L))

theorem surjective_finite_morphism_ample
    (X Y S : AlgebraicSpace.{u}) (f : SpaceHom Y X) (pX : SpaceHom X S)
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (L : SheafObj X)
    (hX : IsProper pX) (hS_noetherian : Prop) (hf : IsFinite f)
    (hs : IsSurjective f)
    (hL : IsInvertible L) :
    Nonempty (FiniteSurjectiveAmpleStatement X Y f L) := by
  sorry

end Formalization.«Books.SpacesCohomology».Unit01
