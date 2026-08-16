import Formalization.Books.SpacesCohomology.Unit01.VanishingAboveDimension

/-!
# Cohomology and base change, I
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure BaseChangeData {X Y Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y) (F : SheafObj X) where
  X' : AlgebraicSpace.{u}
  projection : SpaceHom X' X
  f' : SpaceHom X' Y'
  F' : SheafObj X'
  cartesian : Prop

structure AffineBaseChangeStatement {X Y Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y) (F : SheafObj X) where
  direct_image_is_derived : Prop
  direct_image_quasi_coherent : IsQuasiCoherent (pushforwardSheaf f F)
  base_change : Nonempty (SheafIso Y'
    (pullbackSheaf g (pushforwardSheaf f F))
    (pushforwardSheaf (baseChangeTarget f g) (pullbackSheaf (baseChangeSource f g) F)))

theorem affine_base_change
    (S X Y Y' : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hAffine : IsAffine f)
    (g : SpaceHom Y' Y) (F : SheafObj X) (hF : IsQuasiCoherent F) :
    Nonempty (AffineBaseChangeStatement f g F) := by
  sorry

structure FlatBaseChangeStatement {X Y X' Y' : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (g : SpaceHom Y' Y)
    (f' : SpaceHom X' Y') (g' : SpaceHom X' X) (F : SheafObj X) where
  cartesian : Prop
  sheaf_base_change : ∀ i : ℕ, Nonempty (SheafIso Y'
    (pullbackSheaf g (higherDirectImage i f F))
    (higherDirectImage i f' (pullbackSheaf g' F)))
  cohomology_base_change : Prop

theorem flat_base_change_cohomology
    (S X Y X' Y' : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (g : SpaceHom Y' Y)
    (f' : SpaceHom X' Y') (g' : SpaceHom X' X)
    (hcart : Prop) (hflat : IsFlat g) (hqc : IsQuasiCompact f)
    (hqs : IsQuasiSeparated f) (F : SheafObj X) (hF : IsQuasiCoherent F) :
    Nonempty (FlatBaseChangeStatement f g f' g' F) := by
  sorry

structure SplitSheafHom {X Y : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (F : SheafObj X) where
  map : SheafHom (pullbackSheaf f (pushforwardSheaf f F)) F
  section_ : SheafHom F (pullbackSheaf f (pushforwardSheaf f F))
  section_map_id : Prop

theorem etale_pull_push_split
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hqc : IsQuasiCompact f)
    (hsep : IsSeparated f) (hetale : IsEtale f)
    (F : SheafObj X) (hF : IsQuasiCoherent F) :
    Nonempty (SplitSheafHom f F) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
