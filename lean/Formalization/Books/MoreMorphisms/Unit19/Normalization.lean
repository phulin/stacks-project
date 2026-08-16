/-
# More on Morphisms, Chapter 19: absolute normalization
-/

import Formalization.Books.MoreMorphisms.Unit19.SmoothBaseChange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization

namespace MoreMorphisms.Unit19

open AlgebraicGeometry CategoryTheory Limits

universe u

/-!
Mathlib's normalization is relative.  The normalization of the identity map
is the canonical absolute normalization used by the source notation `X^ν`.
-/

noncomputable def absoluteNormalization (X : Scheme.{u}) : Scheme.{u} :=
  (𝟙 X : X ⟶ X).normalization

noncomputable def absoluteNormalizationMap (X : Scheme.{u}) :
    absoluteNormalization X ⟶ X :=
  (𝟙 X : X ⟶ X).fromNormalization

/-!
The finiteness hypothesis in the source is stated explicitly as a property of
all quasi-compact open subschemes.
-/

def FiniteIrreducibleComponentsOnQuasiCompactOpens (X : Scheme.{u}) : Prop :=
  ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite

theorem smooth_preserves_finite_irreducible_components
    (f : X ⟶ Y) [Smooth f]
    (hY : FiniteIrreducibleComponentsOnQuasiCompactOpens Y) :
    FiniteIrreducibleComponentsOnQuasiCompactOpens X := by
  sorry

theorem normalization_and_smooth
    (f : X ⟶ Y) [Smooth f]
    (hY : FiniteIrreducibleComponentsOnQuasiCompactOpens Y) :
    ∃! e : absoluteNormalization X ≅
        pullback (absoluteNormalizationMap Y) f,
      e.hom ≫ pullback.snd (absoluteNormalizationMap Y) f =
        absoluteNormalizationMap X := by
  sorry

end MoreMorphisms.Unit19
