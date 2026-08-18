import Formalization.Books.Duality.Unit22.DualizingModules

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def IsCohenMacaulayScheme (X : Scheme.{u}) : Prop :=
  ∃ K : DerivedObject X, IsDualizingComplexOn K ∧ IsBounded K

theorem lemma_dualizing_module_CM_scheme {X : Scheme.{u}}
    (hcm : IsCohenMacaulayScheme X) : ∃ K : DerivedObject X, IsDualizingModule K := by
  sorry

theorem lemma_has_dualizing_module_CM_scheme {X : Scheme.{u}}
    (hcm : IsCohenMacaulayScheme X) : ∃ K : DerivedObject X, IsDualizingModule K := by
  sorry

theorem lemma_affine_flat_Noetherian_CM {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hflat : IsFlatMorphism f) (hnoetherian : IsNoetherianScheme Y)
    (hcm : IsCohenMacaulayScheme Y) : IsCohenMacaulayScheme X := by
  sorry

def remark_CM_morphism_compare_dualizing {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsCohenMacaulayScheme X ∧ IsCohenMacaulayScheme Y

end

end Formalization.Books.Duality.Unit01
