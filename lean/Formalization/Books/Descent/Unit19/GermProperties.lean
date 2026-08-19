import Formalization.Books.Descent.Unit19.Core
import Mathlib.RingTheory.AlgebraicIndependent.Basic

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Formalization.Books.Descent.Unit19

abbrev GermSchemeProperty := SchemeMorphismProperty

def StableUnderEtalePrecomposition (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), Etale f → P g → P (f ≫ g)

def EtaleLocalAtSourceAndTarget (P : SchemeMorphismProperty) : Prop :=
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    P f ↔ ∀ x : X, ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y)
      (h : U ⟶ V) (u : U), Etale a ∧ Etale b ∧
        a ≫ f = h ≫ b ∧ a u = x ∧ P h

def IsEtaleLocalOnSourceAndTarget (P : SchemeMorphismProperty) : Prop :=
  StableUnderEtalePrecomposition P ∧
    PreservedByBaseChange (@Etale) P ∧ EtaleLocalAtSourceAndTarget P

def germPropertyOfSchemeProperty (P : SchemeMorphismProperty) :
    SchemeGerm.GermMorphismProperty :=
  fun {X Y} f => ∃ g : SchemeGerm.Hom X Y, g.map = f.map ∧ P g.map

def germOfSchemeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    SchemeGerm.Hom ⟨X, x⟩ ⟨Y, f x⟩ :=
  ⟨f, rfl⟩

def SchemePropertyIsEtaleLocalOnSourceAndTarget
    (P : SchemeMorphismProperty) : Prop :=
  IsEtaleLocalOnSourceAndTarget P

def GermPropertyIsEtaleLocalOnSourceAndTarget
    (Q : SchemeGerm.GermMorphismProperty) : Prop :=
  SchemeGerm.IsEtaleLocalOnGerms Q

theorem global_property_implies_local_germ_property
    (P : SchemeMorphismProperty)
    (hP : SchemePropertyIsEtaleLocalOnSourceAndTarget P) :
    GermPropertyIsEtaleLocalOnSourceAndTarget
      (germPropertyOfSchemeProperty P) := by sorry

theorem local_germ_property_implies_global_property
    (P : SchemeMorphismProperty)
    (hP : SchemePropertyIsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∀ x : X,
      germPropertyOfSchemeProperty P
        (germOfSchemeHom f x) := by
  constructor
  · intro hf x
    exact ⟨germOfSchemeHom f x, rfl, hf⟩
  · intro h
    by_cases hX : Nonempty X
    · obtain ⟨g, hg, hPg⟩ := h hX.some
      rw [hg] at hPg
      exact hPg
    · have hlocal := (show IsEtaleLocalOnSourceAndTarget P from hP).2.2 f
      apply hlocal.mpr
      intro x
      exact (hX ⟨x⟩).elim

theorem flatAtPoint_isEtaleLocalOnSourceAndTarget :
    SchemeGerm.IsEtaleLocalOnGerms (fun {X Y} f => SchemeGerm.Hom.IsFlatAtPoint f) := by
  sorry

/-
noncomputable def fibreMap
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (comm : a ≫ h = h' ≫ b) (v' : V') :
    h'.fiber v' ⟶ h.fiber (b v') :=
  pullback.lift
    (h'.fiberι v' ≫ a)
    (h'.fiberToSpecResidueField v' ≫ Spec.map (b.residueFieldMap v'))
    (by
      rw [Category.assoc, Category.assoc, comm]
      rw [h'.fiber_fac_assoc]
      rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField])

theorem etale_on_fibre
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (comm : a ≫ h = h' ≫ b) (ha : Etale a) (hb : Etale b) (v' : V') :
    Etale (fibreMap a b h' h comm v') := by sorry

def FibreLocalRingDimensionProperty (d : WithBot ℕ∞) :
    SchemeGerm.GermMorphismProperty :=
  fun {_X _Y} f => f.fibreLocalRingDimension = d

def ResidueFieldTranscendenceDegreeProperty (r : Cardinal) :
    SchemeGerm.GermMorphismProperty :=
  fun {_X _Y} f => f.residueFieldTranscendenceDegree = r

def FibrePointDimensionProperty (d : ℕ∞) :
    SchemeGerm.GermMorphismProperty :=
  fun {_X _Y} f => f.fibrePointDimension = d

theorem fibre_local_ring_dimension_is_etale_local (d : WithBot ℕ∞) :
    SchemeGerm.IsEtaleLocalOnGerms (FibreLocalRingDimensionProperty d) := by sorry

theorem residue_field_transcendence_degree_is_etale_local (r : Cardinal) :
    SchemeGerm.IsEtaleLocalOnGerms
      (ResidueFieldTranscendenceDegreeProperty r) := by sorry

theorem fibre_point_dimension_is_etale_local (d : ℕ∞) :
    SchemeGerm.IsEtaleLocalOnGerms (FibrePointDimensionProperty d) := by sorry

end Formalization.Books.Descent.Unit19
-/
