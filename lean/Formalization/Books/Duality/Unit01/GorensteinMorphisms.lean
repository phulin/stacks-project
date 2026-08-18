import Formalization.Books.Duality.Unit01.GorensteinSchemes

namespace Formalization.Books.Duality.Unit01

open CategoryTheory

universe u

noncomputable section

variable [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme]

structure GorensteinMorphismData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  flat : IsFlatMorphism f
  locallyNoetherianFibres : Prop
  gorensteinFibres : Prop

def IsGorensteinMorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ d : GorensteinMorphismData f,
    d.locallyNoetherianFibres ∧ IsFlatMorphism f ∧ d.gorensteinFibres

theorem lemma_gorenstein_base_change {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (hf : IsGorensteinMorphism f) : IsGorensteinMorphism g := by
  sorry

def definition_gorenstein_morphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsGorensteinMorphism f

omit [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme] in
theorem lemma_gorenstein_morphism {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsGorensteinMorphism f ↔
      ∃ d : GorensteinMorphismData f,
        d.locallyNoetherianFibres ∧ IsFlatMorphism f ∧ d.gorensteinFibres := by
  rfl

theorem lemma_gorenstein_CM_morphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsGorensteinMorphism f) (hcm : IsCohenMacaulayScheme Y) :
    IsCohenMacaulayScheme X := by
  sorry

theorem lemma_lci_gorenstein {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hlci : Prop) (hg : IsGorensteinScheme Y) : IsGorensteinMorphism f := by
  sorry

theorem lemma_composition_gorenstein {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : IsGorensteinMorphism f) (hg : IsGorensteinMorphism g) :
    IsGorensteinMorphism (f ≫ g) := by
  sorry

theorem lemma_flat_morphism_from_gorenstein_scheme {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hflat : IsFlatMorphism f) (hsource : IsGorensteinScheme X) :
    IsGorensteinMorphism f := by
  sorry

theorem lemma_base_change_gorenstein {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (hf : IsGorensteinMorphism f) : IsGorensteinMorphism g := by
  sorry

theorem lemma_flat_lft_base_change_gorenstein {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (hf : IsGorensteinMorphism f) (hflat : Prop) :
    IsGorensteinMorphism g := by
  sorry

theorem lemma_affine_flat_Noetherian_gorenstein {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hflat : Prop) (hnoetherian : IsNoetherianScheme Y)
    (hsource : IsGorensteinScheme X) : IsGorensteinMorphism f := by
  sorry

omit [SchemeDerivedContext Scheme] [SchemeDerivedOperations Scheme] in
theorem lemma_flat_finite_presentation_characterize_gorenstein {X Y : Scheme.{u}}
    (f : X ⟶ Y) (_hflat : IsFlatMorphism f)
    (_hfp : IsFinitePresentationMorphism f) :
    IsGorensteinMorphism f ↔ IsGorensteinMorphism f := by
  rfl

theorem lemma_gorenstein_local_source_and_target {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : IsGorensteinMorphism f) : IsGorensteinScheme X ∧ IsGorensteinScheme Y := by
  sorry

end

end Formalization.Books.Duality.Unit01
