import Formalization.«Books.Descent».Unit33.PropertiesOfMorphismsOfGerms

universe u

open CategoryTheory
open AlgebraicGeometry

namespace SchemeGerm

/-!
# Descent, Chapter 33

This chapter formalizes “Properties of morphisms of germs local on
source-and-target”.  The imported section file contains the chosen-germ
interfaces and real constructions; the theorem statements below follow the
source order and are left for the proof stage.
-/

/-- Source Lemma `lemma-local-source-target-global-implies-local`. -/
lemma globalProperty_implies_localGermProperty
    (P : SchemeMorphismProperty)
    (hP : IsEtaleLocalOnSourceAndTargetScheme P) :
    IsEtaleLocalOnSourceAndTarget (germPropertyOfSchemeProperty P) := by
  sorry

/-- Source Lemma `lemma-local-source-target-local-implies-global`. -/
lemma localGermProperty_implies_globalProperty
    (P : SchemeMorphismProperty)
    (hP : IsEtaleLocalOnSourceAndTargetScheme P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P f ↔ ∀ x : X, germPropertyOfSchemeProperty P (Hom.ofSchemeHom f x) := by
  sorry

/-! ### Flatness at a point -/

/-- Source Lemma `lemma-flat-at-point`. -/
lemma flatAtPoint_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (fun {X Y} f => Hom.IsFlatAtPoint f) := by
  sorry

/-! ### Étale morphisms on fibres -/

/-- Source Lemma `lemma-etale-on-fiber`. -/
lemma etaleOnFibre
    {U' U V' V : Scheme.{u}}
    (a : U' ⟶ U) (b : V' ⟶ V) (h' : U' ⟶ V') (h : U ⟶ V)
    (comm : a ≫ h = h' ≫ b) (ha : Etale a) (hb : Etale b) (v' : V') :
    Etale (fibreMap a b h' h comm v') := by
  sorry

/-! ### Dimension of the local ring of a fibre -/

/-- Source Lemma `lemma-dimension-local-ring-fibre`. -/
lemma fibreLocalRingDimension_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.fibreLocalRingDimension f = d) := by
  sorry

/-! ### Transcendence degree at a point -/

/-- Source Lemma `lemma-transcendence-degree-at-point`.

The parameter is a `Cardinal`, which is the canonical Mathlib codomain of
transcendence degree and also covers extensions of uncountable transcendence
degree.
-/
lemma residueFieldTranscendenceDegree_isEtaleLocalOnSourceAndTarget (r : Cardinal) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.residueFieldTranscendenceDegree f = r) := by
  sorry

/-! ### Dimension at a point -/

/-- Source Lemma `lemma-dimension-at-point`. -/
lemma fibrePointDimension_isEtaleLocalOnSourceAndTarget (d : ℕ∞) :
    IsEtaleLocalOnSourceAndTarget
      (fun {X Y} f => Hom.fibrePointDimension f = d) := by
  sorry

end SchemeGerm
