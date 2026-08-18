import Formalization.Books.Duality.Unit01.MoreDualizingComplexes

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure ProperOverFieldDualityData {X : Scheme.{u}} where
  field : Prop
  proper : Prop
  dualizing : DerivedObject X
  dualizingProperty : IsDualizingComplexOn dualizing
  pairing : ∀ K : DerivedObject X, Isomorphic K
    (InternalHom dualizing (InternalHom dualizing K))

theorem lemma_duality_proper_over_field {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) :
    ∀ K : DerivedObject X, Isomorphic K
      (InternalHom d.dualizing (InternalHom d.dualizing K)) := by
  exact d.pairing

def remark_duality_proper_over_field {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) : Prop :=
  d.field ∧ d.proper

def remark_coherent_duality_proper_over_field {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) : Prop :=
  IsCoherent d.dualizing

theorem lemma_duality_proper_over_field_perfect {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) (hperfect : Prop) :
    ∀ K : DerivedObject X, Isomorphic K
      (InternalHom d.dualizing (InternalHom d.dualizing K)) := by
  exact d.pairing

theorem lemma_duality_proper_over_field_CM {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) (hcm : IsCohenMacaulayScheme X) :
    IsDualizingComplexOn d.dualizing := by
  exact d.dualizingProperty

def remark_rework_duality_locally_free_CM {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) : Prop :=
  IsCohenMacaulayScheme X

theorem lemma_sanity_check_duality {X : Scheme.{u}}
    (d : ProperOverFieldDualityData (X := X)) :
    Isomorphic (StructureSheaf X)
      (InternalHom d.dualizing d.dualizing) := by
  sorry

end

end Formalization.Books.Duality.Unit01
