import Formalization.Books.Homology.Unit25.DoubleComplexes

/-!
# Obsolete, Chapter 3: Homological algebra

The source section is a remark recalling the weak-Serre-subcategory
consequence of the first-quadrant spectral-sequence results.  Its three
substantive assertions are exposed below through the canonical spectral
sequence and filtered-complex interfaces from Homology Chapters 24 and 25.
The source's editorial warning that these assertions are obsolete is
recorded here as documentation rather than as a mathematical declaration.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Formalization.Books.Homology.Unit18
open Formalization.Books.Homology.Unit24
open Formalization.Books.Homology.Unit25

universe v u

namespace Formalization.Books.Obsolete.Unit03

/-! ## Weak Serre subcategories and spectral sequences -/

/-- The source's first-spectral-sequence assertion for a first-quadrant
double complex.  `HasFiniteDiagonalSupport` is the source's finite
diagonal hypothesis, and `P.IsWeakSerreClass` is Mathlib's canonical
weak-Serre-subcategory interface. -/
theorem weak_serre_subcategory_first_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (K : DoubleComplex C)
    (hK : HasFiniteDiagonalSupport K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ,
      P ((doubleComplexFirstSpectralSequence K).page r (p, q))) :
    ∀ n : ℤ, P (doubleComplexFirstTotalCohomology K n) := by
  exact doubleComplex_first_quadrant_weak_serre_first K hK r P hP

/-- The identical source assertion for the second spectral sequence of a
first-quadrant double complex. -/
theorem weak_serre_subcategory_second_spectral_sequence
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasCountableCoproducts C] (K : DoubleComplex C)
    (hK : HasFiniteDiagonalSupport K) (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ,
      P ((doubleComplexSecondSpectralSequence K).page r (p, q))) :
    ∀ n : ℤ, P (doubleComplexSecondTotalCohomology K n) := by
  exact doubleComplex_first_quadrant_weak_serre_second K hK r P hP

/-- The source's filtered-complex assertion: finite filtrations give the
biregular spectral-sequence convergence situation, and membership of one
page in a weak Serre class forces membership of every cohomology object. -/
theorem weak_serre_subcategory_filtered_complex
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredComplex C)
    (hK : FilteredComplexFiniteFiltration K)
    (r : ℕ)
    (P : ObjectProperty C) [P.IsWeakSerreClass]
    (hP : ∀ p q : ℤ,
      P ((filteredComplexSpectralSequence K).page r (p, q))) :
    ∀ n : ℤ, P (filteredComplexCohomology K n) := by
  exact filteredComplex_finite_filtration_weak_serre_membership K hK
    (filteredComplexSpectralSequence K) r P hP

end Formalization.Books.Obsolete.Unit03
