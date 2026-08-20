import Formalization.Books.SpacesCohomology.Unit02.Core

/-!
# Descent, Chapter 19: Variants on descending properties

This file contains the presentation-level algebraic-space interface needed by
the regularity statement. The project’s established algebraic-space interface
is reused, with a chapter-local regularity predicate because that interface
does not yet provide one.
-/

universe u

namespace Formalization.Books.Descent.Unit19

namespace AlgebraicSpaceInterface

abbrev Space := Formalization.Books.SpacesCohomology.Unit01.AlgebraicSpace
abbrev Hom := Formalization.Books.SpacesCohomology.Unit01.SpaceHom
abbrev AlgebraicSpaceTheory :=
  Formalization.Books.SpacesCohomology.Unit01.AlgebraicSpaceTheory

class RegularSpaceTheory [AlgebraicSpaceTheory.{u}] where
  isRegular : Space.{u} → Prop

def IsRegular (X : Space.{u}) [AlgebraicSpaceTheory.{u}]
    [RegularSpaceTheory.{u}] : Prop :=
  RegularSpaceTheory.isRegular X

def IsLocallyOfFinitePresentation {X Y : Space.{u}} (f : Hom X Y)
    [AlgebraicSpaceTheory.{u}] : Prop :=
  Formalization.Books.SpacesCohomology.Unit01.IsLocallyOfFinitePresentation f

def IsFlat {X Y : Space.{u}} (f : Hom X Y) [AlgebraicSpaceTheory.{u}] : Prop :=
  Formalization.Books.SpacesCohomology.Unit01.IsFlat f

def IsSurjective {X Y : Space.{u}} (f : Hom X Y) : Prop :=
  Formalization.Books.SpacesCohomology.Unit01.IsSurjective f

end AlgebraicSpaceInterface

end Formalization.Books.Descent.Unit19
