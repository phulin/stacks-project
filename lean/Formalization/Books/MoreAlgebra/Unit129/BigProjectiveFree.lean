/-
# More on Algebra, Chapter 129: Big projective modules are free
-/

import Formalization.Books.Algebra.Unit84.TransfiniteDevissage
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Defs

namespace Formalization.Books.MoreAlgebra.Unit129

noncomputable section

universe u v

/-! ## Source-facing predicates -/

/- The source's `P_𝔪` is the canonical module localization at a maximal ideal.
   Its rank is a cardinal, so `aleph0 ≤ rank` expresses infinite rank without
   choosing a finite-rank encoding. -/

/-- Every maximal localization of `M` has infinite module rank. -/
def HasInfiniteMaximalRank
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
  ∀ m : MaximalSpectrum R,
    Cardinal.aleph0 ≤
      Module.rank (Localization.AtPrime m.asIdeal)
        (LocalizedModule m.asIdeal.primeCompl M)

/-! ## Eilenberg's lemma and its first consequence -/

/-- Eilenberg's swindle: a non-finitely generated free module absorbs a summand. -/
theorem eilenberg_swindle
    {R : Type u} {P Q F : Type v} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Module.Free R F]
    (hF : ¬ Module.Finite R F)
    (hPQ : Nonempty ((P × Q) ≃ₗ[R] F)) :
    Nonempty ((P × F) ≃ₗ[R] F) := by
  sorry

/-- A projective module becomes free after adjoining a suitable free module. -/
theorem projective_plus_free_is_free
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P] :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F),
      Module.Free R F ∧ Module.Free R (P × F) := by
  sorry

/-! ## Finite free pieces containing elements -/

/-- An element of a projective module is contained in a finite free direct summand
of a finite-free enlargement.  Finite free modules are written canonically as
`Fin n →₀ R`. -/
theorem element_projective
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (s : P) :
    ∃ n : ℕ, ∃ K : Submodule R ((Fin n →₀ R) × P),
      (0, s) ∈ K ∧ IsComplemented K ∧
        Module.Finite R K ∧ Module.Free R K := by
  sorry

/-! ## Finding a unimodular element -/

/-- If `s` together with a submodule `M` generates `P`, one can adjust `s` by
an element of `M` to obtain a rank-one free direct summand. -/
theorem trick_to_find_good_element
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) (M : Submodule R P)
    (hgen : Submodule.span R ({s} : Set P) ⊔ M = ⊤) :
    ∃ m : P, m ∈ M ∧
      IsComplemented (Submodule.span R ({s + m} : Set P)) ∧
        Nonempty (R ≃ₗ[R] Submodule.span R ({s + m} : Set P)) := by
  sorry

/-! ## Finite stably free summands -/

/-- Every element of a projective module satisfying the Jacobson and rank
hypotheses lies in a finite stably-free direct summand. -/
theorem element_in_free_summand
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : HasInfiniteMaximalRank R P) (s : P) :
    ∃ M : Submodule R P, s ∈ M ∧ IsComplemented M ∧
      Module.Finite R M ∧ Module.IsStablyFree R M := by
  sorry

/-! ## Countably generated projective modules -/

/-- A countably generated projective module of infinite rank at every maximal
localization is free. -/
theorem countable_free
    {R : Type u} {P : Type v} [CommRing R]
    (hR : IsNoetherianRing (R ⧸ Ring.jacobson R))
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hPgen : Formalization.Books.Algebra.Unit84.Module.IsCountablyGenerated R P)
    (hP : HasInfiniteMaximalRank R P) :
    Module.Free R P := by
  sorry

end

end Formalization.Books.MoreAlgebra.Unit129
