import Formalization.Books.SpacesCohomology.Unit01.WeakChow
import Mathlib.Algebra.Ring.Basic

/-!
# Noetherian valuative criterion
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure DVRData where
  ring : Type u
  commRing : CommRing ring
  domain : Prop
  dvr : Prop
  fractionField : Type u
  fractionField_is_field : Prop
  fraction_field_property : Prop

structure ValuativeDiagram (X Y : AlgebraicSpace.{u})
    (f : SpaceHom X Y) where
  dvr : DVRData
  commutative : Prop
  generic_map : Prop
  special_map : Prop
  lift : Type u

def AtMostOneDVRLift {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ D : ValuativeDiagram X Y f, D.commutative → D.special_map →
    Subsingleton D.lift

def UniqueDVRLift {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ D : ValuativeDiagram X Y f, D.commutative → D.special_map →
    Nonempty D.lift ∧ Subsingleton D.lift

theorem check_separated_dvr
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}]
    (hY : IsLocallyNoetherian Y) (hft : IsLocallyOfFiniteType f)
    (hqs : IsQuasiSeparated f) (h : AtMostOneDVRLift f) :
    IsSeparated f := by
  sorry

theorem check_proper_dvr
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}]
    (hY : IsLocallyNoetherian Y) (hft : IsFiniteType f)
    (hqs : IsQuasiSeparated f) (h : UniqueDVRLift f) :
    IsProper f := by
  sorry

structure CompleteValuativeDiagram (X Y : AlgebraicSpace.{u})
    (f : SpaceHom X Y) where
  dvr : DVRData
  complete : Prop
  commutative : Prop
  generic_map : Prop
  special_map : Prop
  lift : Type u

def AtMostOneCompleteDVRLift {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ D : CompleteValuativeDiagram X Y f, D.commutative → D.special_map →
    Subsingleton D.lift

def CompleteDVRExistenceAfterExtension
    {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y) : Prop :=
  ∀ D : CompleteValuativeDiagram X Y f, D.commutative → D.special_map →
    ∃ D' : CompleteValuativeDiagram X Y f,
      D'.commutative ∧ D'.special_map ∧ Nonempty D'.lift ∧
        Subsingleton D'.lift

theorem complete_dvr_separated_variant
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}]
    (hY : IsLocallyNoetherian Y) (hft : IsLocallyOfFiniteType f)
    (hqs : IsQuasiSeparated f) (h : AtMostOneCompleteDVRLift f) :
    IsSeparated f := by
  sorry

theorem complete_dvr_proper_variant
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y)
    [AlgebraicSpaceTheory.{u}]
    (hY : IsLocallyNoetherian Y) (hft : IsFiniteType f)
    (hqs : IsQuasiSeparated f) (h : CompleteDVRExistenceAfterExtension f) :
    IsProper f := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
