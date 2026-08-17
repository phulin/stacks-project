import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Exercises, Chapter 7: Localization

This file records the finite-module localization exercise.  A zero module is
represented by the canonical `Subsingleton` predicate, and principal module
localization uses `LocalizedModule (Submonoid.powers f) M`.
-/

noncomputable section

universe u v

namespace Formalization.Books.Exercises.Unit07

/-! ## A finite module killed by one principal localization -/

/-- If a finite module becomes zero after localization at `S`, then one
element of `S` already kills its principal localization. -/
theorem exists_principal_localization_subsingleton_of_localization_subsingleton
    {A : Type u} [CommRing A] (S : Submonoid A)
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hM : Subsingleton (LocalizedModule S M)) :
    ∃ f : A, f ∈ S ∧
      Subsingleton (LocalizedModule (Submonoid.powers f) M) := by
  sorry

end Formalization.Books.Exercises.Unit07
