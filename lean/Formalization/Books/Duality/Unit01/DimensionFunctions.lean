import Formalization.Books.Duality.Unit01.Glueing

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure NormalizedDualizingData (X : Scheme.{u}) where
  complex : DerivedObject X
  dualizing : IsDualizingComplexOn complex
  normalized : Prop

structure DualizingDimensionData (X : Scheme.{u}) (d : NormalizedDualizingData X) where
  dimensionFunction : SchemeDerivedContext.supportLabel X → ℤ
  isDimensionFunction : IsDimensionFunction dimensionFunction

theorem lemma_good_dualizing_normalized {X : Scheme.{u}}
    (d : NormalizedDualizingData X) : Nonempty (NormalizedDualizingData X) := by
  exact ⟨d⟩

theorem lemma_good_dualizing_dimension_function {X : Scheme.{u}}
    (d : NormalizedDualizingData X) : Nonempty (DualizingDimensionData X d) := by
  sorry

theorem lemma_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (d : NormalizedDualizingData Y) :
    IsDualizingComplexOn (a.rightAdjoint.obj d.complex) := by
  sorry

theorem lemma_flat_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hflat : IsFlatMorphism f) (K : DerivedObject Y) :
    IsDualizingComplexOn (a.rightAdjoint.obj K) := by
  sorry

theorem lemma_shriek_over_CM {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hcm : Prop) :
    IsDualizingComplexOn (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

theorem lemma_flat_quasi_finite_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hflat : IsFlatMorphism f)
    (hquasiFinite : IsLocallyQuasiFiniteMorphism f) :
    IsDualizingComplexOn (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

theorem lemma_CM_shriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hcm : Prop) :
    IsDualizingComplexOn (a.rightAdjoint.obj (StructureSheaf Y)) := by
  sorry

def remark_the_same_is_true {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsProperMorphism f

end

end Formalization.Books.Duality.Unit01
