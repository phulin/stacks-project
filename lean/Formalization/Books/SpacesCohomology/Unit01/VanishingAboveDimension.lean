import Formalization.Books.SpacesCohomology.Unit01.CohomologySupport

/-!
# Vanishing above the dimension
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

open CategoryTheory

variable [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]

def restrictionSurjective {X U : AlgebraicSpace.{u}}
    (j : SpaceHom U X) (F : SheafObj X) (d : ℕ) : Prop :=
  ∃ φ : CohomologyGroup X F d → CohomologyGroup U (restrictSheaf j F) d,
    Function.Surjective φ

theorem cohomology_vanishes_above_dimension
    (S X : AlgebraicSpace.{u}) (hS : IsScheme S)
    (hqc : IsQuasiCompact (𝟙 X : SpaceHom X X))
    (hqs : IsQuasiSeparated (𝟙 X : SpaceHom X X))
    (d : ℕ) (hd : SpaceDimension X ≤ d)
    (F : SheafObj X) (hF : IsQuasiCoherent F)
    (U : OpenSubspace X) (hU : IsQuasiCompact U.inclusion)
    (Z : ClosedSubspace X) (C : ClosedSubspaceComplement X Z)
    (hZ : IsQuasiCompact C.open_subspace.inclusion)
    (TZ : SupportTheory X Z) :
    (∀ q : ℕ, d < q → CohomologyVanishes X F q) ∧
    restrictionSurjective U.inclusion F d ∧
    (∀ q : ℕ, d < q → Subsingleton (supportCohomologyGroup TZ F q)) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
