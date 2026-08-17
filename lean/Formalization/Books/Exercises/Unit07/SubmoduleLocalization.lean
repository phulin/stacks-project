import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Exercises, Chapter 7: Localization

This file records the submodule-localization exercise.  Mathlib's canonical
`Submonoid`, `LocalizedModule`, and `Submodule.localized` constructions give
the source notation `S⁻¹A`, `S⁻¹M`, and `S⁻¹N'` directly.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit07

/-! ## Submodules of a localization -/

/-- Every submodule of a localized module is the localization of an
`A`-submodule. -/
theorem exists_submodule_localizing
    {A : Type u} [CommRing A] (S : Submonoid A)
    {M : Type v} [AddCommGroup M] [Module A M]
    (N : Submodule (Localization S) (LocalizedModule S M)) :
    ∃ N' : Submodule A M, N = N'.localized S := by
  sorry

end Formalization.Books.Exercises.Unit07
