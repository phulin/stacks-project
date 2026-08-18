import Formalization.Books.Duality.Unit17.UpperShriekProperties

namespace Formalization.Books.Duality.Unit01

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure ShriekBaseChangeData (square : CartesianSquare Scheme)
    (a : RightAdjointData square.f) (a' : RightAdjointData square.f') where
  map : ∀ K : DerivedObject square.Y,
    (LPullback square.g').obj (a.rightAdjoint.obj K) ⟶
      a'.rightAdjoint.obj ((LPullback square.g).obj K)

def IsIsoShriekBaseChange {square : CartesianSquare Scheme}
    {a : RightAdjointData square.f} {a' : RightAdjointData square.f'}
    (b : ShriekBaseChangeData square a a') : Prop :=
  ∀ K, IsIso (b.map K)

theorem lemma_base_change_shriek_flat {square : CartesianSquare Scheme}
    (a : RightAdjointData square.f) (a' : RightAdjointData square.f')
    (b : ShriekBaseChangeData square a a') (hflat : IsFlatMorphism square.g) :
    IsIsoShriekBaseChange b := by
  sorry

theorem lemma_shriek_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hetale : IsEtaleMorphism f) :
    UpperShriekRestrictsToPullback f a := by
  sorry

theorem lemma_base_change_locally {square : CartesianSquare Scheme}
    (a : RightAdjointData square.f) (a' : RightAdjointData square.f')
    (b : ShriekBaseChangeData square a a') (hlocal : Prop) :
    IsIsoShriekBaseChange b := by
  sorry

theorem lemma_relative_dualizing_fibres {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hflat : IsFlatMorphism f) :
    IsDualizingComplexOn (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

end

end Formalization.Books.Duality.Unit01
