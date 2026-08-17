import Formalization.Books.Exercises.Unit24.Core
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Exercises, Chapter 24: Going up and going down

This file records the source-facing interfaces for the definition and the
three numbered exercises.  Proposition proofs are deferred to the proving
stage; the underlying rings, maps, and answer sets are defined in `Core`.
-/

noncomputable section

universe u

open Set

namespace Formalization.Books.Exercises.Unit24

/-! ## Definition `GU-GD` -/

/-- The explicit prime-spectrum form of the going-up definition in the source.

`GoingUpProperty` itself reuses Mathlib's canonical algebraic predicate; this
equivalence exposes the source's quantifiers over prime spectra and its
"lying over" terminology. -/
theorem goingUpProperty_iff_primeSpectrum
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    GoingUpProperty φ ↔
      ∀ {p p' : PrimeSpectrum A}, p.asIdeal ≤ p'.asIdeal →
        ∀ {P : PrimeSpectrum B}, LiesOver φ p P →
          ∃ P' : PrimeSpectrum B,
            LiesOver φ p' P' ∧ P.asIdeal ≤ P'.asIdeal := by
  sorry

/-- The explicit prime-spectrum form of the going-down definition in the
source. -/
theorem goingDownProperty_iff_primeSpectrum
    {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) :
    GoingDownProperty φ ↔
      ∀ {p p' : PrimeSpectrum A}, p.asIdeal ≤ p'.asIdeal →
        ∀ {P' : PrimeSpectrum B}, LiesOver φ p' P' →
          ∃ P : PrimeSpectrum B,
            LiesOver φ p P ∧ P.asIdeal ≤ P'.asIdeal := by
  sorry

/-! ## Exercise `GU-GD` -/

/- The seven declarations below preserve the hypotheses and record the
   determination requested for each item of the source exercise. -/

/-- Case (1): `k → k[x]` has both going-up and going-down. -/
theorem exercise_GU_GD_case_one (k : Type u) [Field k] :
    GoingUpProperty (fieldToPolynomialMap k) ∧
      GoingDownProperty (fieldToPolynomialMap k) := by
  sorry

/-- Case (2): `k[x] → k[x,y]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_two (k : Type u) [Field k] :
    ¬ GoingUpProperty (polynomialToBivariateMap k) ∧
      GoingDownProperty (polynomialToBivariateMap k) := by
  sorry

/-- Case (3): `ℤ → ℤ[1/11]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_three :
    ¬ GoingUpProperty integerToLocalizationAt11 ∧
      GoingDownProperty integerToLocalizationAt11 := by
  sorry

/-- Case (4): the displayed integral polynomial tower has going-up but not
going-down; its map has kernel `(y-x²)`. -/
theorem exercise_GU_GD_case_four (k : Type u) [Field k] [IsAlgClosed k] :
    GoingUpProperty (algebraicTowerMap k) ∧
      ¬ GoingDownProperty (algebraicTowerMap k) := by
  sorry

/-- Case (5): `ℤ → ℤ[i,1/(2+i)]` has both properties. -/
theorem exercise_GU_GD_case_five :
    GoingUpProperty integerToGaussianLocalizationAtTwoPlusI ∧
      GoingDownProperty integerToGaussianLocalizationAtTwoPlusI := by
  sorry

/-- Case (6): `ℤ → ℤ[i,1/(14+7i)]` has going-down but not going-up. -/
theorem exercise_GU_GD_case_six :
    ¬ GoingUpProperty integerToGaussianLocalizationAtFourteenPlusSevenI ∧
      GoingDownProperty integerToGaussianLocalizationAtFourteenPlusSevenI := by
  sorry

/-- Case (7): the idempotent-localized quotient has going-down but not
going-up. -/
theorem exercise_GU_GD_case_seven (k : Type u) [Field k] [IsAlgClosed k] :
    ¬ GoingUpProperty (idempotentLocalizationMap k) ∧
      GoingDownProperty (idempotentLocalizationMap k) := by
  sorry

/-! ## Exercise `image` -/

/-- The image of `D(f)` under `Spec(A[X]) → Spec(A)` is the union of the
basic opens of all coefficients of `f`.  Coefficients outside the finite
support are zero, so the indexed union is the source's finite union
`D(a₀) ∪ ⋯ ∪ D(aᵣ)`. -/
theorem image_basicOpen_polynomial_eq_iUnion_coefficients
    {A : Type*} [CommRing A] (f : Polynomial A) :
    PrimeSpectrum.comap (Polynomial.C : A →+* Polynomial A) ''
        (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (Polynomial A))) =
      ⋃ i : ℕ,
        (PrimeSpectrum.basicOpen (f.coeff i) : Set (PrimeSpectrum A)) := by
  rw [Polynomial.image_comap_C_basicOpen]
  ext p
  simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    Set.mem_iUnion]
  rw [Set.not_subset]
  simp

/-! ## Exercise `images` -/

/-- Image computation (1): `Spec(k[x,yx⁻¹]) → Spec(k[x,y])`. -/
theorem exercise_images_case_one (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (reciprocalImageMap k)) =
      reciprocalImageAnswer k := by
  sorry

/-- Image computation (2): `Spec(k[x,y,a,b]/(ax-by-1)) → Spec(k[x,y])`. -/
theorem exercise_images_case_two (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (unitEquationMap k)) =
      unitEquationImageAnswer k := by
  sorry

/-- Image computation (3): the localized cusp parameterization. -/
theorem exercise_images_case_three (k : Type u) [Field k] [IsAlgClosed k] :
    Set.range (PrimeSpectrum.comap (cuspParameterMap k)) =
      cuspImageAnswer k := by
  sorry

/-- Image computation (4): the complex cubic curve mapped by squaring both
coordinates. -/
theorem exercise_images_case_four :
    Set.range (PrimeSpectrum.comap cubicSquareMap) = cubicImageAnswer := by
  sorry

end Formalization.Books.Exercises.Unit24

end
