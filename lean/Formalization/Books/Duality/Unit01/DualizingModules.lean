import Formalization.Books.Duality.Unit01.DimensionFunctions

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure DualizingModuleData {X : Scheme.{u}} where
  module : DerivedObject X
  ambientComplex : DerivedObject X
  dualizing : IsDualizingComplexOn ambientComplex
  moduleComparison : Isomorphic module ambientComplex

def IsDualizingModule {X : Scheme.{u}} (K : DerivedObject X) : Prop :=
  ∃ d : DualizingModuleData, Isomorphic K d.module

theorem example_proper_over_local {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : RightAdjointData f) (hlocal : Prop) :
    Nonempty (DualizingModuleData (X := X)) := by
  sorry

theorem example_equidimensional_over_field {X : Scheme.{u}}
    (hfield : Prop) (hequidimensional : Prop) :
    Nonempty (DualizingModuleData (X := X)) := by
  sorry

theorem lemma_dualizing_module {X : Scheme.{u}} (K : DerivedObject X)
    (hdualizing : IsDualizingComplexOn K) : IsDualizingModule K := by
  sorry

theorem lemma_vanishing_good_dualizing {X : Scheme.{u}}
    (d : DualizingModuleData (X := X)) (hvanishing : Prop) :
    IsDualizingModule d.module := by
  exact ⟨d, ⟨Iso.refl d.module⟩⟩

theorem lemma_dualizing_module_proper_over_A {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : RightAdjointData f) (hproper : IsProperMorphism f) :
    IsDualizingModule (RelativeDualizingComplex f a) := by
  sorry

end

end Formalization.Books.Duality.Unit01
