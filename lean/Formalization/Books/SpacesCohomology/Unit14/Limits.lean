import Formalization.Books.SpacesCohomology.Unit13.Devissage

/-!
# Limits of coherent modules
-/

namespace Formalization.Books.SpacesCohomology.Unit01

universe u

structure FilteredCoherentSubmoduleColimit (X : AlgebraicSpace.{u})
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) where
  index : Type u
  nonempty_index : Nonempty index
  filtered : Prop
  term : index → SheafObj X
  coherent : ∀ i, IsCoherentModule X (term i)
  inclusion : ∀ i, SheafHom (term i) F
  colimit_property : Prop

theorem directed_colimit_coherent
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X : AlgebraicSpace.{u}) (F : SheafObj X)
    (_hX : IsNoetherian X) (_hF : IsQuasiCoherent F) :
    Nonempty (FilteredCoherentSubmoduleColimit X F) := by
  sorry

structure FilteredFinitePresentationColimit
    {X Y : AlgebraicSpace.{u}} (f : SpaceHom X Y)
    [AlgebraicSpaceCohomology.{u}] (F : SheafObj X) where
  index : Type u
  nonempty_index : Nonempty index
  filtered : Prop
  term : index → SheafObj X
  finitely_presented : ∀ i, IsFinitePresentation (term i)
  colimit_property : Prop

theorem direct_colimit_finite_presentation
    [AlgebraicSpaceTheory.{u}] [AlgebraicSpaceCohomology.{u}]
    (X Y : AlgebraicSpace.{u}) (f : SpaceHom X Y) (F : SheafObj X)
    (_hY : IsNoetherian Y) (_hf : IsAffine f) (_hF : IsQuasiCoherent F) :
    Nonempty (FilteredFinitePresentationColimit f F) := by
  sorry

end Formalization.Books.SpacesCohomology.Unit01
