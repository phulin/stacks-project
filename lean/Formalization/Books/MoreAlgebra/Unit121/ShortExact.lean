/-
# More on Algebra, Chapter 121: the short-exact-sequence formulas
-/

import Formalization.Books.MoreAlgebra.Unit121.Core
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

namespace Formalization.Books.MoreAlgebra.Unit121

noncomputable section

open CategoryTheory

universe u v

/-!
`ShortComplex.ShortExact` is Mathlib's canonical interface for a short exact sequence.  In
particular, the sequence below is a short complex in the abelian category of pairs, so the
commuting endomorphism data are retained by the morphisms themselves.
-/

theorem lemma_ses_det
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    determinant S.X₂ = determinant S.X₁ * determinant S.X₃ := by
  sorry

theorem lemma_ses_trace
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    trace S.X₂ = trace S.X₁ + trace S.X₃ := by
  sorry

theorem lemma_ses_characteristicPolynomial
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    characteristicPolynomial S.X₂ =
      characteristicPolynomial S.X₁ * characteristicPolynomial S.X₃ := by
  sorry

/-- The three identities of the source lemma collected in one interface. -/
theorem lemma_ses
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : ShortComplex (FiniteLengthEndomorphism.{u, v} R)}
    (hS : S.ShortExact) :
    determinant S.X₂ = determinant S.X₁ * determinant S.X₃ ∧
      trace S.X₂ = trace S.X₁ + trace S.X₃ ∧
        characteristicPolynomial S.X₂ =
          characteristicPolynomial S.X₁ * characteristicPolynomial S.X₃ := by
  exact ⟨lemma_ses_det hS, lemma_ses_trace hS, lemma_ses_characteristicPolynomial hS⟩

end
