import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Exercises, Chapter 63: Injectives

The source hypothesis is the standard injectivity class for the regular module
and the conclusion is expressed using the canonical residue field.
-/

namespace Formalization.Books.Exercises.Unit63

universe u

noncomputable section

/-- The `A`-module of maps from the residue field to the regular module. -/
abbrev ResidueFieldHomModule (A : Type u) [CommRing A] [IsLocalRing A] :=
  IsLocalRing.ResidueField A →ₗ[A] A

/-- A self-injective Artinian local ring has one-dimensional socle.  The
length over `A` is the residue-field dimension here. -/
theorem residue_field_hom_dimension_one
    (A : Type u) [CommRing A] [IsArtinianRing A] [IsLocalRing A]
    [Module.Injective A A] :
    Module.length A (ResidueFieldHomModule A) = 1 := by
  sorry

end

end Formalization.Books.Exercises.Unit63
