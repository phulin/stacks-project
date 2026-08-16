import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback

/-!
# Morphisms of Algebraic Spaces, Chapter 53: universal homeomorphisms

The algebraic-space development is not yet present in this project snapshot.
This file records the topological and categorical interfaces used by the
chapter, with `TopCat` as the underlying category of spaces.
-/

namespace Formalization.Books.SpacesMorphisms.Unit53

open CategoryTheory
open CategoryTheory.Limits

abbrev AlgebraicSpace := TopCat

abbrev AlgebraicSpaceMorphism (X Y : AlgebraicSpace) := X ⟶ Y

abbrev AlgebraicSpaceOver (S : AlgebraicSpace) := Over S

end Formalization.Books.SpacesMorphisms.Unit53
