import Formalization.Books.Duality.Unit23.CohenMacaulay

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

def IsGorensteinScheme (X : Scheme.{u}) : Prop :=
  ∃ K : DerivedObject X, IsDualizingComplexOn K ∧ IsInvertibleObject K

def definition_gorenstein (X : Scheme.{u}) : Prop :=
  IsGorensteinScheme X

theorem lemma_gorenstein_CM {X : Scheme.{u}} (h : IsGorensteinScheme X) :
    IsCohenMacaulayScheme X := by
  sorry

theorem lemma_regular_gorenstein {X : Scheme.{u}} (hregular : Prop) :
    IsGorensteinScheme X := by
  sorry

theorem lemma_gorenstein {X : Scheme.{u}} (hcm : IsCohenMacaulayScheme X)
    (hinvertible : Prop) : IsGorensteinScheme X := by
  sorry

theorem lemma_gorenstein_lci {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hlci : Prop) (hgorensteinTarget : IsGorensteinScheme Y) :
    IsGorensteinScheme X := by
  sorry

theorem lemma_gorenstein_local_syntomic {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hsyntomic : Prop) (hgorensteinTarget : IsGorensteinScheme Y) :
    IsGorensteinScheme X := by
  sorry

end

end Formalization.Books.Duality.Unit01
