import Formalization.Books.Exercises.Unit19.Core

import Mathlib.RingTheory.Localization.FractionRing

/-!
# Exercises, Chapter 19: Fraction fields

This file records the domain assertion and the fraction-field identification
requested by the chapter's single exercise.  The proofs are deferred to the
proving stage.
-/

namespace Formalization.Books.Exercises.Unit19

noncomputable section

/-! ## Exercise `find-fraction-field` -/

/- The source calls the displayed quotient a domain.  Recording that fact as
   an instance makes Mathlib's canonical `FractionRing` a field here. -/
instance sourceRing_isDomain : IsDomain sourceRing := by
  sorry

/- The explicit plane curve is a domain, as required by the requested form
   `ℚ[x, y]/(f)`. -/
instance planeCurveRing_isDomain : IsDomain planeCurveRing := by
  sorry

/-- The source quotient has the same fraction field as the displayed plane
curve with `y = s + t`. -/
theorem source_fraction_field_equiv_plane_curve :
    Nonempty (FractionRing sourceRing ≃+* FractionRing planeCurveRing) := by
  sorry

end

end Formalization.Books.Exercises.Unit19
