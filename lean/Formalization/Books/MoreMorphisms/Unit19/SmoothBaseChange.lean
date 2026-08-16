/-
# More on Morphisms, Chapter 19: normalization and smooth base change
-/

import Formalization.Books.MoreMorphisms.Unit19.IntegralClosure
import Mathlib.AlgebraicGeometry.Normalization

namespace MoreMorphisms.Unit19

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {X S Y : Scheme.{u}}

/-!
For the canonical pullback square, Mathlib constructs the comparison map from
the normalization of the pullback to the pullback of the normalization.
-/

noncomputable def normalizationSmoothBaseChangeIso
    (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f] [Smooth g] :
    (pullback.snd f g).normalization ≅ pullback f.fromNormalization g :=
  asIso (f.normalizationPullback g)

/-!
This is the displayed fibre-square statement, with an arbitrary pullback
realization `Y₂` retained in the interface.
-/

theorem normalization_smooth_base_change
    {Y₂ Y₁ X₂ X₁ : Scheme.{u}}
    (f₂ : Y₂ ⟶ X₂) (f₁ : Y₁ ⟶ X₁) (φ : X₂ ⟶ X₁) (ψ : Y₂ ⟶ Y₁)
    (h : IsPullback ψ f₂ f₁ φ) [QuasiCompact f₁] [QuasiSeparated f₁] [Smooth φ] :
    letI : QuasiCompact f₂ :=
      MorphismProperty.of_isPullback h inferInstance
    letI : QuasiSeparated f₂ :=
      MorphismProperty.of_isPullback h inferInstance
    ∃ e : f₂.normalization ≅ pullback f₁.fromNormalization φ,
      e.hom ≫ pullback.snd f₁.fromNormalization φ = f₂.fromNormalization := by
  sorry

end MoreMorphisms.Unit19
