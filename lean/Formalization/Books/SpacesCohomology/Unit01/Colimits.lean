import Formalization.Books.SpacesCohomology.Unit01.FiniteMorphisms

/-!
# Colimits and cohomology
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

structure FilteredSheafColimit (X : AlgebraicSpace.{u}) where
  index : Type u
  nonempty_index : Nonempty index
  object : index → SheafObj X
  colimit : SheafObj X
  filtered : Prop
  colimit_property : Prop

structure FilteredGroupColimit (D : FilteredSheafColimit X) (p : ℤ) where
  carrier : Type u
  group : AddCommGroup carrier
  canonical_comparison : Prop

instance filteredGroupColimitGroup {D : FilteredSheafColimit X} {p : ℤ}
    (C : FilteredGroupColimit D p) : AddCommGroup C.carrier := C.group

structure FilteredImageColimit {X Y : AlgebraicSpace.{u}}
    (f : SpaceHom X Y) (p : ℕ) (D : FilteredSheafColimit X) where
  colimit : SheafObj Y
  colimit_property : Prop

theorem filtered_colimits_cohomology
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (hqc : IsQuasiCompact (𝟙 X : SpaceHom X X))
    (hqs : IsQuasiSeparated (𝟙 X : SpaceHom X X))
    (D : FilteredSheafColimit X) (p : ℤ)
    (C : FilteredGroupColimit D p) :
    Nonempty (C.carrier ≃+ CohomologyGroup X D.colimit p) := by
  sorry

theorem higher_direct_images_commute_filtered_colimits
    (S X Y : AlgebraicSpace.{u}) (hS : IsScheme S)
    (f : SpaceHom X Y) (hqc : IsQuasiCompact f) (hqs : IsQuasiSeparated f)
    (D : FilteredSheafColimit X) (p : ℕ)
    (L : FilteredImageColimit f p D) :
    Nonempty (SheafIso Y (higherDirectImage p f D.colimit) L.colimit) := by
  sorry

theorem finite_presentation_hom_commutes_filtered_colimits
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (hqc : IsQuasiCompact (𝟙 X : SpaceHom X X))
    (hqs : IsQuasiSeparated (𝟙 X : SpaceHom X X))
    (G : SheafObj X) (hG : IsFinitePresentation G)
    (D : FilteredSheafColimit X)
    (C : FilteredGroupColimit D 0) :
    Nonempty (C.carrier ≃+ SheafHom G D.colimit) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
