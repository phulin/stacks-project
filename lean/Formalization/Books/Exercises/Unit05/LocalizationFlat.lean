import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the localization exercise.  A multiplicative subset is
represented by Mathlib's canonical `Submonoid`; localized modules and their
tensor-product model are likewise the canonical Mathlib constructions.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit05

open scoped TensorProduct

/-! ## Localization is flat -/

/-- The source's equality
`S⁻¹M = S⁻¹A ⊗[A] M`, expressed by the canonical linear equivalence over
`S⁻¹A`. -/
noncomputable def localizedModuleTensorProductEquiv
    {A : Type u} [CommRing A] (S : Submonoid A)
    (M : Type v) [AddCommGroup M] [Module A M] :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[A] M :=
  LocalizedModule.equivTensorProduct S M

/-- Localization at a multiplicative subset is flat over the original ring. -/
theorem localization_flat
    {A : Type u} [CommRing A] (S : Submonoid A) :
    Module.Flat A (Localization S) := by
  exact IsLocalization.flat (Localization S) S

end Formalization.Books.Exercises.Unit05
