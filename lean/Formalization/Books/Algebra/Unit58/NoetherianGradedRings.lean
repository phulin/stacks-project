import Formalization.Books.Algebra.Unit55.KGroups
import Formalization.Books.Algebra.Unit56.GradedRings
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.GradedAlgebra.FiniteType
import Mathlib.RingTheory.GradedAlgebra.Noetherian
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Commutative Algebra, Chapter 58: Noetherian graded rings

The graded-ring and graded-module data are the canonical wrappers from Chapter
56.  The numerical-polynomial interface records eventual agreement on the
integer line, and Hilbert functions take values in the set-sized `KPrimeZero`
model from Chapter 55.
-/

namespace Formalization.Books.Algebra.Unit58

open Formalization.Books.Algebra.Unit55
open Formalization.Books.Algebra.Unit56
open scoped BigOperators

universe u v

noncomputable section

variable {S : Type u} [CommRing S]
variable {M : Type v} [AddCommGroup M] [Module S M]

/-! ## Noetherian graded rings -/

/- The source's `S₊` is the irrelevant ideal from Chapter 56. -/

theorem sPlus_generated_iff
    {ι : Type v} (G : GradedRingData S) (f : ι → S)
    (hf : ∀ i, IsHomogeneousElement G (f i) ∧ f i ∈ irrelevantIdeal G) :
    (Algebra.adjoin (degreeZeroSubring G) (Set.range f) =
        (⊤ : Subalgebra (degreeZeroSubring G) S)) ↔
      Ideal.span (Set.range f) = irrelevantIdeal G := by
  sorry

theorem graded_noetherian_iff (G : GradedRingData S) :
    IsNoetherianRing S ↔
      IsNoetherianRing (degreeZeroSubring G) ∧ (irrelevantIdeal G).FG := by
  sorry

theorem finiteType_of_noetherian_graded
    (G : GradedRingData S) (hS : IsNoetherianRing S) :
    Algebra.FiniteType (degreeZeroSubring G) S := by
  sorry

/-! ## Numerical polynomials -/

/-- The integer binomial coefficient used in the eventual formula below.

The value at negative integers is immaterial to an eventual statement; it is
set to zero so that this is a total function on `ℤ`. -/
def integerBinomial (n : ℤ) (i : ℕ) : ℤ :=
  if 0 ≤ n then (n.toNat.choose i : ℤ) else 0

/-- A function on the integers is a numerical polynomial if it is eventually
of binomial-coefficient form with coefficients in an abelian group. -/
def IsNumericalPolynomial {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ r : ℕ, ∃ a : ℕ → A,
    ∀ᶠ n : ℤ in Filter.atTop,
      f n = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i

/-- A numerical polynomial with a prescribed upper bound on the index of its
binomial expansion. -/
def IsNumericalPolynomialOfDegreeLessThan
    {A : Type v} [AddCommGroup A] (f : ℤ → A) (d : ℕ) : Prop :=
  ∃ r : ℕ, r < d ∧ ∃ a : ℕ → A,
    ∀ᶠ n : ℤ in Filter.atTop,
      f n = ∑ i ∈ Finset.range (r + 1), integerBinomial n i • a i

/-- Eventual vanishing, used for the zero-polynomial exception in the
one-variable quotient statement. -/
def IsEventuallyZero {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∀ᶠ n : ℤ in Filter.atTop, f n = 0

theorem numericalPolynomial_comp_addMonoidHom
    {A A' : Type v} [AddCommGroup A] [AddCommGroup A']
    (φ : A →+ A') (f : ℤ → A) (hf : IsNumericalPolynomial f) :
    IsNumericalPolynomial (fun n => φ (f n)) := by
  sorry

theorem isNumericalPolynomial_of_sub
    {A : Type v} [AddCommGroup A] (f : ℤ → A)
    (hf : IsNumericalPolynomial (fun n => f n - f (n - 1))) :
    IsNumericalPolynomial f := by
  sorry

/- The elementary integer-valued-polynomial fact recalled in the source. -/
theorem integer_valued_polynomial_is_numerical
    (P : Polynomial ℚ)
    (hP : ∀ n : ℤ, ∃ z : ℤ, P.eval (n : ℚ) = (z : ℚ)) :
    ∃ f : ℤ → ℤ,
      (∀ n : ℤ, (f n : ℚ) = P.eval (n : ℚ)) ∧
        IsNumericalPolynomial f := by
  sorry

theorem shifted_integerBinomial_is_numerical (i : ℕ) :
    IsNumericalPolynomial (fun n : ℤ => integerBinomial (n + 1) (i + 1)) := by
  sorry

/-! ## Finitely generated graded modules and Hilbert functions -/

/- A degree-zero scalar preserves each graded component.  Chapter 56 records
the components as additive subgroups, so this is the small module instance
needed by the K′₀ construction. -/
instance gradedComponentDegreeZeroModule
    (G : GradedRingData S) (𝓜 : GradedModuleData G M) (n : ℤ) :
    Module (degreeZeroSubring G) (𝓜.component n) where
  smul r x :=
    ⟨(r : S) • (x : M), by
      have h := 𝓜.gradedSMul.smul_mem r.property x.property
      change (r : S) • (x : M) ∈ 𝓜.component ((0 : ℤ) + n) at h
      simpa using h⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : S) • (x : M) = (x : M)
    simp
  mul_smul r s x := by
    apply Subtype.ext
    change ((r : S) * (s : S)) • (x : M) = (r : S) • ((s : S) • (x : M))
    exact mul_smul (r : S) (s : S) (x : M)
  smul_add r x y := by
    apply Subtype.ext
    change (r : S) • ((x : M) + (y : M)) =
      (r : S) • (x : M) + (r : S) • (y : M)
    simp
  smul_zero r := by
    apply Subtype.ext
    change (r : S) • (0 : M) = 0
    simp
  add_smul r s x := by
    apply Subtype.ext
    change ((r : S) + (s : S)) • (x : M) =
      (r : S) • (x : M) + (s : S) • (x : M)
    exact add_smul (r : S) (s : S) (x : M)
  zero_smul x := by
    apply Subtype.ext
    change (0 : S) • (x : M) = 0
    simp

theorem graded_module_component_finite
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    [Algebra.FiniteType (degreeZeroSubring G) S] [Module.Finite S M] :
    ∀ n : ℤ, Module.Finite (degreeZeroSubring G) (𝓜.component n) := by
  sorry

noncomputable def gradedHilbertFunction
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (h𝓜 : ∀ n : ℤ, Module.Finite (degreeZeroSubring G) (𝓜.component n)) :
    ℤ → KPrimeZero (degreeZeroSubring G) :=
  fun n =>
    letI : Module.Finite (degreeZeroSubring G) (𝓜.component n) := h𝓜 n
    kPrimeZeroClass (R := degreeZeroSubring G) (M := 𝓜.component n)

noncomputable def noetherianGradedHilbertFunction
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M] :
    ℤ → KPrimeZero (degreeZeroSubring G) := by
  letI : Algebra.FiniteType (degreeZeroSubring G) S :=
    finiteType_of_noetherian_graded G hS
  exact gradedHilbertFunction G 𝓜 (graded_module_component_finite G 𝓜)

/-- The irrelevant ideal is generated in degree one. -/
def GeneratedInDegreeOne (G : GradedRingData S) : Prop :=
  ∃ t : Set S, (∀ x ∈ t, x ∈ G.component 1) ∧
    Ideal.span t = irrelevantIdeal G

theorem graded_hilbert_polynomial
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    (hdegree : GeneratedInDegreeOne G) :
    IsNumericalPolynomial (noetherianGradedHilbertFunction G 𝓜 hS) := by
  sorry

/-- A function is periodic-polynomial when its restriction to every residue
class modulo one positive period is a numerical polynomial in the quotient
variable. -/
def IsPeriodicNumericalPolynomial
    {A : Type v} [AddCommGroup A] (f : ℤ → A) : Prop :=
  ∃ q : ℕ, 0 < q ∧
    ∀ r : Fin q,
      IsNumericalPolynomial (fun m : ℤ => f ((r : ℤ) + (q : ℤ) * m))

theorem graded_hilbert_periodic_polynomial
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    (hnot : ¬ GeneratedInDegreeOne G) :
    IsPeriodicNumericalPolynomial (noetherianGradedHilbertFunction G 𝓜 hS) := by
  sorry

/- The field-valued example uses the existing K′₀-to-dimension theorem from
Chapter 55. -/
noncomputable def degreeZeroHilbertFunctionLength
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    [IsArtinianRing (degreeZeroSubring G)] : ℤ → ℤ :=
  fun n =>
    kPrimeZeroLength (R := degreeZeroSubring G)
      (noetherianGradedHilbertFunction G 𝓜 hS n)

theorem graded_hilbert_function_length_numerical
    (G : GradedRingData S) (𝓜 : GradedModuleData G M)
    (hS : IsNoetherianRing S) [Module.Finite S M]
    [IsArtinianRing (degreeZeroSubring G)]
    (hdegree : GeneratedInDegreeOne G) :
    IsNumericalPolynomial (degreeZeroHilbertFunctionLength G 𝓜 hS) := by
  sorry

theorem field_kprimeZero_length_eq_finrank
    {k : Type u} [Field k] {N : Type v}
    [AddCommGroup N] [Module k N] [Module.Finite k N] :
    kPrimeZeroLength (R := k)
        (kPrimeZeroClass (R := k) (M := N)) =
      (Module.finrank k N : ℤ) := by
  exact kPrimeZeroLength_field_eq_finrank

/-! ## The polynomial-ring quotient example -/

abbrev polynomialQuotientComponent
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) (n : ℕ) : Type u :=
  MvPolynomial.homogeneousSubmodule (Fin d) k n ⧸
    Submodule.comap
      (MvPolynomial.homogeneousSubmodule (Fin d) k n).subtype
      (I.restrictScalars k)

def polynomialQuotientHilbertFunction
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) : ℤ → ℤ :=
  fun n =>
    if _h : 0 ≤ n then
      (Module.finrank k (polynomialQuotientComponent k d I n.toNat) : ℤ)
    else 0

def IsPolynomialGradedIdeal
    (k : Type u) [Field k] (d : ℕ)
    (I : Ideal (MvPolynomial (Fin d) k)) : Prop :=
  ∀ n : ℕ, ∀ x : MvPolynomial (Fin d) k, x ∈ I →
    MvPolynomial.homogeneousComponent n x ∈ I

theorem polynomial_quotient_hilbert_function_degree_lt
    (k : Type u) [Field k] (d : ℕ) (hd : 0 < d)
    (I : Ideal (MvPolynomial (Fin d) k)) (hI : I ≠ ⊥)
    (hIgraded : IsPolynomialGradedIdeal k d I) :
    IsNumericalPolynomialOfDegreeLessThan
        (polynomialQuotientHilbertFunction k d I) (d - 1) ∨
      (d = 1 ∧
        IsEventuallyZero (polynomialQuotientHilbertFunction k d I)) := by
  sorry

end

end Formalization.Books.Algebra.Unit58
