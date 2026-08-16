/-
# More on Morphisms, Chapter 19: normalization and henselization
-/

import Formalization.«Books.MoreMorphisms».Unit19.Normalization
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Henselian

namespace MoreMorphisms.Unit19

open AlgebraicGeometry CategoryTheory Limits

universe u

/-!
Mathlib contains the Henselian local-ring property but not the henselization
or strict henselization constructions.  The following source-facing
interfaces record their standard local universal properties so that the
scheme statement can be stated without replacing those constructions by an
unrelated smooth or localization hypothesis.
-/

def IsHenselization
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) : Prop :=
  IsLocalHom f ∧
    ∀ (C : Type u) [CommRing C] [HenselianLocalRing C],
      ∀ (g : A →+* C), IsLocalHom g →
        ∃! h : B →+* C, IsLocalHom h ∧ h.comp f = g

def IsStrictHenselization
    (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) : Prop :=
  IsLocalHom f ∧ HenselianLocalRing B ∧ IsSepClosed (IsLocalRing.ResidueField B) ∧
    ∀ (C : Type u) [CommRing C] [HenselianLocalRing C]
      [IsSepClosed (IsLocalRing.ResidueField C)],
      ∀ (g : A →+* C), IsLocalHom g →
        ∃! h : B →+* C, IsLocalHom h ∧ h.comp f = g

/-!
The two maps from the spectra of the henselization and strict henselization
are obtained by composing the corresponding spectrum map with the canonical
map from the spectrum of the local ring to `X`.
-/

noncomputable def henselizationMap
    (X : Scheme.{u}) (x : X) {A : CommRingCat.{u}}
    (f : X.presheaf.stalk x ⟶ A) : Spec A ⟶ X :=
  Spec.map f ≫ X.fromSpecStalk x

theorem normalization_henselization
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X)
    {Aʰ Aˢʰ : CommRingCat.{u}}
    (ιʰ : X.presheaf.stalk x ⟶ Aʰ) (ιˢʰ : X.presheaf.stalk x ⟶ Aˢʰ)
    (hʰ : IsHenselization (X.presheaf.stalk x) Aʰ ιʰ.hom)
    (hˢʰ : IsStrictHenselization (X.presheaf.stalk x) Aˢʰ ιˢʰ.hom) :
    IsIso ((pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ιʰ)).toNormalization) ∧
    IsIso ((pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ιˢʰ)).toNormalization) := by
  sorry

end MoreMorphisms.Unit19
