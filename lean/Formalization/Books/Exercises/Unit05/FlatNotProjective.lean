import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Exercises, Chapter 5: Flat ring maps

This file records the finite flat non-projective example and the warning that
finite presentation rules out such an example.  The exercise asks for an
example rather than prescribing a particular presentation, so its existence
is stated with the ring and module as explicit witnesses.
-/

universe u

namespace Formalization.Books.Exercises.Unit05

/-! ## Finite flat modules need not be projective -/

/-- Every finitely presented flat module is projective.  This is the existing
Mathlib theorem used by the source remark. -/
theorem projective_of_flat_of_finitePresentation
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (hflat : Module.Flat A M) (hfinitePresentation : Module.FinitePresentation A M) :
    Module.Projective A M := by
  exact @Module.Flat.projective_of_finitePresentation A M _ _ _ hflat
    hfinitePresentation

/-- There is a finite flat module which is not projective. -/
theorem exists_finite_flat_nonprojective :
    ∃ (A : Type u) (_ : CommRing A) (M : Type u) (_ : AddCommGroup M)
      (_ : Module A M),
      Module.Finite A M ∧ Module.Flat A M ∧ ¬ Module.Projective A M := by
  sorry

/-- Any finite flat non-projective module must be over a non-Noetherian ring. -/
theorem finite_flat_nonprojective_base_not_noetherian
    {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    (hfinite : Module.Finite A M) (hflat : Module.Flat A M)
    (hnotProjective : ¬ Module.Projective A M) :
    ¬ IsNoetherianRing A := by
  sorry

end Formalization.Books.Exercises.Unit05
