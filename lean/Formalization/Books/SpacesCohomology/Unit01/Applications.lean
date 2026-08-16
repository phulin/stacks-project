import Formalization.Books.SpacesCohomology.Unit01.FormalFunctions

/-!
# Applications of the theorem on formal functions
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

def DiscreteGeometricFibres {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ y : Y, IsDiscrete (FibreSpace f y)

def FiniteMorphismsCharacterization {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  IsFinite f ↔ IsProper f ∧ DiscreteGeometricFibres f

theorem characterize_finite
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}] (hY : IsLocallyNoetherian Y) :
    FiniteMorphismsCharacterization f := by
  sorry

structure FiniteNeighbourhoodStatement (X Y : AlgebraicSpace.{u})
    (f : SpaceHom X Y) (y : Y) [AlgebraicSpaceTheory.{u}] where
  neighbourhood : OpenSubspace Y
  contains : OpenContainsPoint neighbourhood y
  inverse_image : AlgebraicSpace.{u}
  restricted_map : SpaceHom inverse_image neighbourhood.carrier
  finite : IsFinite restricted_map
  restriction_property : Prop

theorem proper_finite_fibre_finite_in_neighbourhood
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (y : Y)
    [AlgebraicSpaceTheory.{u}]
    (hY : IsLocallyNoetherian Y) (hf : IsProper f)
    (hfibre : IsFinitePointSet (FibrePoints f y)) :
    Nonempty (FiniteNeighbourhoodStatement X Y f y) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
