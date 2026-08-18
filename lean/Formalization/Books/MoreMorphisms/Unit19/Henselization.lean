/-
# More on Morphisms, Chapter 19: normalization and henselization
-/

import Formalization.Books.MoreMorphisms.Unit19.Normalization
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
    {A_h A_sh : CommRingCat.{u}}
    [IsLocalRing A_h] [IsLocalRing A_sh]
    (ι_h : X.presheaf.stalk x ⟶ A_h) (ι_sh : X.presheaf.stalk x ⟶ A_sh)
    (h_h : IsHenselization (X.presheaf.stalk x) A_h ι_h.hom)
    (h_sh : IsStrictHenselization (X.presheaf.stalk x) A_sh ι_sh.hom)
    [QuasiCompact (pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_h))]
    [QuasiSeparated (pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_h))]
    [QuasiCompact (pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_sh))]
    [QuasiSeparated (pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_sh))] :
    IsIso ((pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_h)).toNormalization) ∧
    IsIso ((pullback.snd (absoluteNormalizationMap X)
      (henselizationMap X x ι_sh)).toNormalization) := by
  sorry

end MoreMorphisms.Unit19
