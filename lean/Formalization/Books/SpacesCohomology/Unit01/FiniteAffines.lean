import Formalization.Books.SpacesCohomology.Unit01.Vanishing

/-!
# Finite morphisms and affines
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory CategoryTheory.Limits

structure FiniteClosedBaseChangeData (X Y Z Z' : AlgebraicSpace.{u})
    (f : SpaceHom Y X) (i : SpaceHom Z X) (i' : SpaceHom Z' Y)
    (f' : SpaceHom Z' Z) [AlgebraicSpaceTheory.{u}] where
  finite : IsFinite f
  surjective : IsSurjective f
  closed_immersion : IsClosedImmersion i
  cartesian : IsPullback f' i' i f
  base_change_map : Prop
  induced_finite_surjective : IsFinite f' ∧ IsSurjective f'
  Z'_locally_noetherian : IsLocallyNoetherian Z'

theorem finite_morphism_noetherian
    (X Y Z Z' : AlgebraicSpace.{u}) (f : SpaceHom Y X) (i : SpaceHom Z X)
    (i' : SpaceHom Z' Y) (f' : SpaceHom Z' Z)
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (D : FiniteClosedBaseChangeData X Y Z Z' f i i' f')
    (hX : IsLocallyNoetherian X) :
    IsCoherentModule Z
        (pushforwardSheaf f' (structureSheaf Z')) ∧
      sheafSupport Z (pushforwardSheaf f' (structureSheaf Z')) =
        Set.range (fun z : Z => z) := by
  sorry

def affineProjectionIdealLeft (X Y : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (f : SpaceHom Y X)
    (I : SheafObj X) (F : SheafObj Y) : SheafObj X :=
  idealTimes X I (pushforwardSheaf f F)

def affineProjectionIdealRight (X Y : AlgebraicSpace.{u})
    [AlgebraicSpaceCohomology.{u}] (f : SpaceHom Y X)
    (I : SheafObj X) (F : SheafObj Y) : SheafObj X :=
  pushforwardSheaf f (idealTimes Y (pullbackSheaf f I) F)

theorem affine_morphism_projection_ideal
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom Y X)
    (I : SheafObj X) (F : SheafObj Y)
    (hf : IsAffine f) (hI : IsQuasiCoherent I) (hF : IsQuasiCoherent F) :
    affineProjectionIdealLeft X Y f I F =
      affineProjectionIdealRight X Y f I F := by
  sorry

structure AffineSpaceWitness (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] where
  scheme : IsScheme X
  affine : IsAffine (𝟙 X : SpaceHom X X)

def IsAffineSchemeSpace (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] : Prop :=
  Nonempty (AffineSpaceWitness X)

theorem image_affine_finite_morphism_affine
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom Y X)
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (hf : IsFinite f) (hs : IsSurjective f) (hY : IsAffineSchemeSpace Y)
    (hX : IsNoetherian X) :
    IsAffineSchemeSpace X := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
