import Formalization.Books.Duality.Unit01.ProperFlat

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def IsPerfectProperMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProperMorphism f ∧
    HasFiniteTorDimension ((LPullback f).obj (StructureSheaf Y))

def PerfectProperComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (K : DerivedObject Y) : Prop :=
  CompareWithPullback f a K

theorem lemma_proper_flat_noetherian {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hnoetherian : IsNoetherianScheme Y)
    (hgeometry : IsProperFlatFinitePresentation f) :
    CommutesWithDirectSums a := by
  sorry

theorem lemma_proper_flat_noetherian_relative {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) (hnoetherian : IsNoetherianScheme Y)
    (hgeometry : IsProperFlatFinitePresentation f) :
    Nonempty (RelativeDualizingProperties f a) := by
  sorry

theorem lemma_compare_with_pullback_flat_proper_noetherian {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) (hnoetherian : IsNoetherianScheme Y)
    (hgeometry : IsProperFlatFinitePresentation f) :
    ∀ K : DerivedObject Y, PerfectProperComparison f a K := by
  sorry

theorem lemma_proper_perfect_base_change {S X Y : Scheme.{u}}
    (square : CartesianSquare Scheme) (a : RightAdjointData square.f)
    (a' : RightAdjointData square.f') (b : BaseChangeData square a a')
    (hperfect : IsPerfectProperMorphism square.f)
    (htor : IsTorIndependent square.f square.g) : IsIsoBaseChange b := by
  sorry

end

end Formalization.Books.Duality.Unit01
